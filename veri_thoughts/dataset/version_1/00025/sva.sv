// SVA for pipelined_xor_gate
// Bind into DUT; references internal regs/wires directly

module pipelined_xor_gate_sva;

  default clocking cb @(posedge clk); endclocking

  bit init;
  initial init = 1'b0;
  always @(posedge clk) init <= 1'b1;

  // Structural/registering checks
  assert property (@cb (a_reg == a && b_reg == b));
  assert property (@cb disable iff (!init) (a_reg1 == $past(a_reg) && b_reg1 == $past(b_reg)));

  // Combinational XOR nets and output wiring
  assert property (@cb (xor_out == (a_reg ^ b_reg)));
  assert property (@cb (xor_out1 == (a_reg1 ^ b_reg1)));
  assert property (@cb (out == xor_out1));
  assert property (@cb disable iff (!init) (out == $past(xor_out)));

  // Functional behavior: 1-cycle latency from inputs to out
  assert property (@cb disable iff (!init)
                   (!$isunknown($past({a,b}))) |-> (!$isunknown(out) && out == ($past(a) ^ $past(b))));

  // Coverage: XOR truth table observed at output (1-cycle later)
  cover property (@cb disable iff (!init) ($past({a,b})==2'b00) && out==1'b0);
  cover property (@cb disable iff (!init) ($past({a,b})==2'b01) && out==1'b1);
  cover property (@cb disable iff (!init) ($past({a,b})==2'b10) && out==1'b1);
  cover property (@cb disable iff (!init) ($past({a,b})==2'b11) && out==1'b0);

  // Coverage: output toggles
  cover property (@cb disable iff (!init) $rose(out));
  cover property (@cb disable iff (!init) $fell(out));

endmodule

bind pipelined_xor_gate pipelined_xor_gate_sva sva_pipelined_xor_gate();