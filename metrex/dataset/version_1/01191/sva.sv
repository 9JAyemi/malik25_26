// SVA for fifo
module fifo_sva
  #(parameter int adr_width = 4,
    parameter int dat_width = 8,
    localparam int depth = (1 << adr_width))
  (
    input  logic                      clk,
    input  logic                      reset,
    // DUT I/Os
    input  logic                      rd,
    input  logic                      wr,
    input  logic [dat_width-1:0]      data_in,
    input  logic [dat_width-1:0]      data_out,
    input  logic                      empty,
    input  logic                      full,
    // DUT internals
    input  logic [dat_width-1:0]      array_reg [depth-1:0],
    input  logic [adr_width-1:0]      w_ptr_reg,
    input  logic [adr_width-1:0]      r_ptr_reg,
    input  logic [adr_width-1:0]      w_ptr_next,
    input  logic [adr_width-1:0]      r_ptr_next,
    input  logic                      full_reg,
    input  logic                      empty_reg,
    input  logic                      full_next,
    input  logic                      empty_next,
    input  logic                      wr_en,
    input  logic [1:0]                orden
  );

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset state on first cycle out of reset
  assert property ($past(reset) && !reset |-> w_ptr_reg == '0 && r_ptr_reg == '0 && full_reg == 1'b0 && empty_reg == 1'b1);

  // Output mirrors internal flags
  assert property (full == full_reg);
  assert property (empty == empty_reg);

  // Flag sanity
  assert property (!(full_reg && empty_reg));
  assert property ((full_reg || empty_reg) |-> (w_ptr_reg == r_ptr_reg));

  // orden must reflect {wr,rd}
  assert property (orden == {wr, rd});

  // wr_en definition and gating
  assert property (wr_en == (wr && !full_reg));
  assert property (full_reg && wr && !rd |-> !wr_en);

  // Data path: data_out reflects memory at r_ptr_reg
  assert property (data_out == array_reg[r_ptr_reg]);

  // Memory write happens exactly when wr_en (check one cycle later)
  assert property ($past(wr_en) |-> array_reg[$past(w_ptr_reg)] == $past(data_in));
  // No write effect when attempting overflow (write on full without read)
  assert property ($past(full_reg && wr && !rd) |-> array_reg[$past(w_ptr_reg)] == $past(array_reg[$past(w_ptr_reg)]));

  // Write-only accepted: increment w_ptr, clear empty, set full iff next equals r_ptr
  assert property (wr && !rd && !full_reg |=> 
                   w_ptr_reg == $past(w_ptr_reg) + 1 &&
                   r_ptr_reg == $past(r_ptr_reg) &&
                   empty_reg == 1'b0 &&
                   ( ($past(w_ptr_reg) + 1 == $past(r_ptr_reg)) ? full_reg : !full_reg ));

  // Read-only accepted: increment r_ptr, clear full, set empty iff next equals w_ptr
  assert property (rd && !wr && !empty_reg |=> 
                   r_ptr_reg == $past(r_ptr_reg) + 1 &&
                   w_ptr_reg == $past(w_ptr_reg) &&
                   full_reg == 1'b0 &&
                   ( ($past(r_ptr_reg) + 1 == $past(w_ptr_reg)) ? empty_reg : !empty_reg ));

  // Overflow attempt blocked
  assert property (wr && !rd && full_reg |=> 
                   $stable(w_ptr_reg) && $stable(r_ptr_reg) && $stable(full_reg) && $stable(empty_reg));

  // Underflow attempt blocked
  assert property (rd && !wr && empty_reg |=> 
                   $stable(w_ptr_reg) && $stable(r_ptr_reg) && $stable(full_reg) && $stable(empty_reg));

  // Simultaneous rd&wr: both pointers advance, flags hold
  assert property (wr && rd |=> 
                   w_ptr_reg == $past(w_ptr_reg) + 1 &&
                   r_ptr_reg == $past(r_ptr_reg) + 1 &&
                   $stable(full_reg) && $stable(empty_reg));

  // Next-state combinational intent (optional consistency)
  assert property (w_ptr_next == ( (orden[1] && !orden[0] && !full_reg) ? w_ptr_reg + 1 :
                                   (orden == 2'b11) ? w_ptr_reg + 1 : w_ptr_next ));
  assert property (r_ptr_next == ( (orden[0] && !orden[1] && !empty_reg) ? r_ptr_reg + 1 :
                                   (orden == 2'b11) ? r_ptr_reg + 1 : r_ptr_next ));

  // Coverages
  cover property (empty_reg && wr && !rd && !full_reg ##1 !empty_reg);                  // leave empty
  cover property (wr && !rd && !full_reg [*depth-1] ##1 full_reg);                      // reach full
  cover property (rd && !wr && !empty_reg [*depth-1] ##1 empty_reg);                    // drain to empty
  cover property (wr && rd);                                                            // simultaneous
  cover property (full_reg && wr && !rd);                                               // overflow attempt
  cover property (empty_reg && rd && !wr);                                              // underflow attempt
  cover property (w_ptr_reg == {adr_width{1'b1}} && wr && !rd && !full_reg ##1 w_ptr_reg == '0); // wrap wptr
  cover property (r_ptr_reg == {adr_width{1'b1}} && rd && !wr && !empty_reg ##1 r_ptr_reg == '0); // wrap rptr

endmodule

// Bind into the DUT
bind fifo fifo_sva #(.adr_width(adr_width), .dat_width(dat_width)) i_fifo_sva (.*);