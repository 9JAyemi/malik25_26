// SVA for top_module
module top_module_sva;

  // Bind into DUT scope; access internal regs/wires directly
  default clocking cb @(posedge clk); endclocking

  // Structural passthrough checks
  assert property (out == out_reg);
  assert property (parity_bit == parity_bit_reg);
  assert property (out_wire == out_reg);
  assert property (parity_bit_wire == parity_bit_reg);

  // Stage 1: inputs captured (1-cycle latency)
  assert property (disable iff (rst)
                   1'b1 |=> (in_hi_reg == $past(in_hi) && in_lo_reg == $past(in_lo)));

  // Stage 2: compute from stage1 regs (1-cycle latency)
  assert property (disable iff (rst)
                   1'b1 |=> (out_reg == {$past(in_hi_reg), $past(in_lo_reg)} &&
                             parity_bit_reg == ($past(in_hi_reg[0]) ^ $past(in_lo_reg[0]))));

  // End-to-end mapping: inputs -> outputs (1-cycle latency)
  assert property (disable iff (rst)
                   1'b1 |=> (out == {$past(in_hi), $past(in_lo)} &&
                             parity_bit == ($past(in_hi[0]) ^ $past(in_lo[0]))));

  // Synchronous reset clears (next cycle)
  assert property (@(posedge clk) rst |=> (in_hi_reg==8'h00 && in_lo_reg==8'h00));
  assert property (@(posedge clk) rst |=> (out_reg==16'h0000 && parity_bit_reg==1'b0));
  assert property (@(posedge clk) rst |=> (out==16'h0000 && parity_bit==1'b0));

  // No X/Z when not in reset
  assert property (disable iff (rst) !$isunknown({in_hi_reg, in_lo_reg, out_reg, out, parity_bit}));

  // Coverage
  cover property (rst ##1 !rst);
  cover property (disable iff (rst) 1'b1 |=> out == {$past(in_hi), $past(in_lo)});
  cover property (disable iff (rst) 1'b1 |=> parity_bit == 1'b0);
  cover property (disable iff (rst) 1'b1 |=> parity_bit == 1'b1);

endmodule

bind top_module top_module_sva sva_top_module();