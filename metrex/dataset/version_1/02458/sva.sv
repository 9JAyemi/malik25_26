// SVA for and_gate
module and_gate_sva(input logic a, input logic b, input logic out);

  // Sample on any relevant signal change
  default clocking cb @(a or b or out); endclocking

  // Functional correctness (includes 4-state behavior)
  assert property (out === (a & b))
    else $error("and_gate: out != (a & b)");

  // If inputs are known, output must be known
  assert property ((!$isunknown({a,b})) |-> (!$isunknown(out)))
    else $error("and_gate: out is X/Z while inputs are known");

  // Functional coverage of all input combinations and expected outputs
  cover property (a===1'b0 && b===1'b0 && out===1'b0);
  cover property (a===1'b0 && b===1'b1 && out===1'b0);
  cover property (a===1'b1 && b===1'b0 && out===1'b0);
  cover property (a===1'b1 && b===1'b1 && out===1'b1);

  // X-propagation coverage when one input is 1 and the other is X/Z
  cover property (a===1'b1 && $isunknown(b) && $isunknown(out));
  cover property (b===1'b1 && $isunknown(a) && $isunknown(out));

endmodule

bind and_gate and_gate_sva sva(.a(a), .b(b), .out(out));