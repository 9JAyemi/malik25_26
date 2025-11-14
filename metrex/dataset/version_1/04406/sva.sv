// SVA checker for low_blk_mem_gen
// Binds a cycle-accurate scoreboard, checks read-first behavior, and key sanity.

module low_blk_mem_gen_sva #(parameter AW=11, DW=12, DEPTH=(1<<AW))
(
  input logic               clka,
  input logic [AW-1:0]      addra,
  input logic [DW-1:0]      dina,
  input logic               wea,
  input logic [DW-1:0]      douta
);

  // Sample after NBA to compare updated DUT outputs
  default clocking cb @(posedge clka);
    input #1step addra, dina, wea, douta;
  endclocking

  // Cycle-accurate scoreboard of memory after each edge
  logic [DW-1:0] exp_mem [0:DEPTH-1];
  bit            valid   [0:DEPTH-1];
  logic [AW-1:0] addra_q;

  initial begin
    for (int i=0;i<DEPTH;i++) begin
      valid[i] = 1'b0;
      exp_mem[i] = '0;
    end
    addra_q = '0;
  end

  always_ff @(posedge clka) begin
    addra_q <= addra;
    if (wea && !$isunknown(addra) && !$isunknown(dina)) begin
      exp_mem[addra] <= dina;
      valid[addra]   <= 1'b1;
    end
  end

  // Inputs should be known when used
  assert property (@cb !$isunknown(wea));
  assert property (@cb !$isunknown(addra));
  assert property (@cb wea |-> !$isunknown(dina));

  // Core behavior: douta equals previous-cycle memory at current address (read-first)
  property p_dout_model;
    $past(valid[addra_q]) |-> (douta === $past(exp_mem[addra_q]));
  endproperty
  assert property (@cb p_dout_model);

  // Read-after-write to same address is visible next cycle
  property p_raw_same_addr_next;
    (wea && !$isunknown(addra) && !$isunknown(dina))
      ##1 (addra == $past(addra)) |-> (douta === $past(dina));
  endproperty
  assert property (@cb p_raw_same_addr_next);

  // Coverage
  cover property (@cb wea);                                                      // any write
  cover property (@cb wea ##1 (wea && (addra == $past(addra))));                 // back-to-back write same addr
  cover property (@cb wea ##1 (addra == $past(addra)));                          // write then read same addr
  cover property (@cb wea && (addra == '0));                                     // write first address
  cover property (@cb wea && (addra == (DEPTH-1)));                              // write last address
  cover property (@cb $past(valid[addra_q]) && (douta === $past(exp_mem[addra_q]))); // observed modeled read

endmodule

// Bind to all instances of low_blk_mem_gen
bind low_blk_mem_gen low_blk_mem_gen_sva #(.AW(11), .DW(12), .DEPTH(2048))
  i_low_blk_mem_gen_sva (.clka(clka), .addra(addra), .dina(dina), .wea(wea), .douta(douta));