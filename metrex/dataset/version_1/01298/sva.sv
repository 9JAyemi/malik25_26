// SVA checker for fifo. Bind this to your DUT.
// Focused, concise, and covers key control, flags, pointers, and write effects.

module fifo_sva
  #(parameter int adr_width = 10,
    parameter int dat_width = 8,
    parameter int depth     = (1 << adr_width))
(
  input  logic                     clk_div,
  input  logic                     reset,
  input  logic                     wr,
  input  logic                     rd,
  input  logic [dat_width-1:0]     data_in,
  input  logic [dat_width-1:0]     data_out,
  input  logic                     empty,
  input  logic                     full,

  // tap internal state
  input  logic [adr_width-1:0]     w_ptr_reg,
  input  logic [adr_width-1:0]     r_ptr_reg,
  input  logic                     full_reg,
  input  logic                     empty_reg,
  input  logic                     wr_en,
  input  logic [dat_width-1:0]     array_reg [depth]
);

  default clocking cb @(posedge clk_div); endclocking
  default disable iff (reset);

  // Basic sanity
  assert property (cb !$isunknown({full, empty, wr, rd})); // flags/controls never X/Z
  assert property (cb !(full && empty));                   // never both set

  // Reset effect (async reset, check after next clk)
  assert property (@(posedge clk_div) $rose(reset) |=> (w_ptr_reg==0 && r_ptr_reg==0 && empty && !full));

  // Write enable gating
  assert property (cb wr_en == (wr && !full));             // en = wr & ~full

  // No state changes on blocked ops
  assert property (cb wr && !rd && full  |=> w_ptr_reg == $past(w_ptr_reg));
  assert property (cb rd && !wr && empty |=> r_ptr_reg == $past(r_ptr_reg));

  // Pointer advances
  assert property (cb wr && !rd && !full |=> w_ptr_reg == $past(w_ptr_reg) + 1);
  assert property (cb rd && !wr && !empty |=> r_ptr_reg == $past(r_ptr_reg) + 1);

  // Simultaneous wr & rd: both pointers advance, flags hold
  assert property (cb wr && rd |=> (w_ptr_reg == $past(w_ptr_reg) + 1)
                                   && (r_ptr_reg == $past(r_ptr_reg) + 1)
                                   && (full == $past(full))
                                   && (empty == $past(empty)));

  // Pointers are idle when no ops
  assert property (cb !wr && !rd |=> (w_ptr_reg == $past(w_ptr_reg)) && (r_ptr_reg == $past(r_ptr_reg)));

  // Flag transitions must be justified by boundary conditions
  assert property (cb $rose(full)  |-> $past(wr && !rd && !full && ((w_ptr_reg + 1) == r_ptr_reg)));
  assert property (cb $fell(full)  |-> $past(rd && !wr)); // cleared only by successful read
  assert property (cb $rose(empty) |-> $past(rd && !wr && !empty && ((r_ptr_reg + 1) == w_ptr_reg)));
  assert property (cb $fell(empty) |-> $past(wr && !rd)); // cleared only by successful write

  // Memory interface correctness
  // Data_out always mirrors array at r_ptr
  assert property (cb data_out == array_reg[r_ptr_reg]);

  // Successful write updates memory at prior write address with prior data
  assert property (cb $past(wr && !full) |-> array_reg[$past(w_ptr_reg)] == $past(data_in));

  // When FIFO is empty and no write, data_out stable
  assert property (cb empty && !wr |=> $stable(data_out));

  // Pointer wrap-around coverage
  cover property (cb $past(wr && !rd && !full) && ($past(w_ptr_reg) == {adr_width{1'b1}}) ##1 (w_ptr_reg == '0));
  cover property (cb $past(rd && !wr && !empty) && ($past(r_ptr_reg) == {adr_width{1'b1}}) ##1 (r_ptr_reg == '0));

  // Corner-case coverage
  cover property (cb $rose(reset));
  cover property (cb $rose(empty));
  cover property (cb $fell(empty));
  cover property (cb $rose(full));
  cover property (cb $fell(full));
  cover property (cb full && wr && !rd);   // blocked write at full
  cover property (cb empty && rd && !wr);  // blocked read at empty
  cover property (cb full && wr && rd);    // simultaneous at full
  cover property (cb empty && wr && rd);   // simultaneous at empty

  // Write-then-read data ordering coverage (eventually read back a written value)
  // Note: this is a cover, not an assertion.
  property p_write_then_readback;
    logic [dat_width-1:0] v;
    (wr && !full, v = data_in)
      ##[1:$] (rd && !empty && data_out == v);
  endproperty
  cover property (cb p_write_then_readback);

endmodule

// Bind example (place in a package or testbench):
// bind fifo fifo_sva #(.adr_width(adr_width), .dat_width(dat_width))
//   u_fifo_sva (.*,
//     .w_ptr_reg(w_ptr_reg),
//     .r_ptr_reg(r_ptr_reg),
//     .full_reg(full_reg),
//     .empty_reg(empty_reg),
//     .wr_en(wr_en),
//     .array_reg(array_reg));