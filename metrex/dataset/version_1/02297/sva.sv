// SVA for top_module
// Bind these checkers to the DUT; concise but high-quality properties.

bind top_module top_module_sva_chk i_top_module_sva_chk();

module top_module_sva_chk;

  // Use DUT scope names directly (via bind)
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (reset |-> (q1 == 1'b0 && q2 == 1'b0))
    else $error("q1/q2 not cleared on reset");

  // Pipeline behavior (mask first cycle after reset)
  assert property (!reset && $past(!reset) |-> q1 == $past(d1))
    else $error("q1 must equal d1 delayed by 1 cycle");

  assert property (!reset && $past(!reset) |-> q2 == $past(d2))
    else $error("q2 must equal d2 delayed by 1 cycle");

  // Internal tracking (JK/T regs track inputs one cycle later)
  assert property ($past(!reset) |-> t1 == $past(d1))
    else $error("t1 should track prior d1");

  assert property ($past(!reset) |-> (j2 == $past(d2) && k2 == ~$past(d2)))
    else $error("j2/k2 should track prior d2 and its complement");

  // JK illegal toggle condition should never occur after pipeline is established
  assert property ($past(!reset) |-> !($past(j2) && $past(k2)))
    else $error("JK toggle state (j2&&k2) must not occur");

  // Combinational outputs
  assert property (out_xor == (in1 ^ in2))
    else $error("out_xor mismatch");

  assert property (out_and == (in1 & in2))
    else $error("out_and mismatch");

  // out_final = out_and | {15'b0, q2} (scalar-bit OR zero-extends)
  assert property (out_final[15:1] == out_and[15:1])
    else $error("out_final[15:1] must match out_and[15:1]");

  assert property (out_final[0] == (out_and[0] | q2))
    else $error("out_final[0] must be out_and[0] OR q2");

  // No X/Z on outputs when not in reset
  assert property (!reset |-> !$isunknown({q1, q2, out_xor, out_and, out_final}))
    else $error("X/Z detected on outputs when not in reset");

  // Coverage
  cover property (!reset && $rose(d1) ##1 q1 == 1'b1);
  cover property (!reset && $fell(d1) ##1 q1 == 1'b0);

  cover property (!reset && $rose(d2) ##1 q2 == 1'b1);
  cover property (!reset && $fell(d2) ##1 q2 == 1'b0);

  cover property (!reset && (in1 != in2) && (out_xor != 16'h0));
  cover property (!reset && (q2 && !out_and[0] && out_final[0])); // q2 drives LSB high
  cover property (!reset && (!q2 && out_and[0] && out_final[0])); // AND drives LSB high

endmodule