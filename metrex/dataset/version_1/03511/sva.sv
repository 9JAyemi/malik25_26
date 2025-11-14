// SVA for nor_gate; bind into the DUT
module nor_gate_sva;
  // Sample whenever inputs change; use ##0 to evaluate after combinational settle
  default clocking cb @(posedge a or negedge a or posedge b or negedge b); endclocking

  // Functional correctness
  assert property (1'b1 |-> ##0 (out === ~(a | b))) else
    $error("NOR functional mismatch: out != ~(a|b)");

  // Gate-by-gate correctness (with known-input guards)
  assert property ((!$isunknown(a)) |-> ##0 (temp1 === ~a)) else
    $error("gate1: temp1 != ~a");
  assert property ((!$isunknown(b)) |-> ##0 (temp2 === ~b)) else
    $error("gate2: temp2 != ~b");
  assert property ((!$isunknown({temp1,temp2})) |-> ##0 (temp3 === ~(temp1 & temp2))) else
    $error("gate3: temp3 != ~(temp1 & temp2)");
  assert property ((!$isunknown(temp3)) |-> ##0 (out === ~temp3)) else
    $error("gate4: out != ~temp3");

  // Redundant cross-check: out equals temp1 & temp2 when inputs are known
  assert property ((!$isunknown({a,b})) |-> ##0 (out === (temp1 & temp2))) else
    $error("out != (temp1 & temp2) with known inputs");

  // No X/Z propagation when inputs are known
  assert property ((!$isunknown({a,b})) |-> ##0 !$isunknown({temp1,temp2,temp3,out})) else
    $error("Unknown on internal/output with known inputs");

  // Coverage: all input combinations with expected out
  cover property (##0 (a===1'b0 && b===1'b0 && out===1'b1));
  cover property (##0 (a===1'b0 && b===1'b1 && out===1'b0));
  cover property (##0 (a===1'b1 && b===1'b0 && out===1'b0));
  cover property (##0 (a===1'b1 && b===1'b1 && out===1'b0));

  // Coverage: output toggles both ways
  cover property ($rose(out));
  cover property ($fell(out));
endmodule

bind nor_gate nor_gate_sva nor_gate_sva_i();