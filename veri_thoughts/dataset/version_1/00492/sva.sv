// SVA for my_module: bindable, clockless, concise, and comprehensive

module my_module_sva (
  input logic Y,
  input logic A1, A2, A3,
  input logic B1, C1
);
  // Functional reference
  let a_and  = (A1 & A2 & A3);
  let y_ref  = ~(B1 | C1 | a_and);

  // Functional equivalence
  assert property (Y === y_ref);

  // Strong consequences of NOR inputs being 1 (robust to X on others)
  assert property (B1 === 1'b1 |-> Y === 1'b0);
  assert property (C1 === 1'b1 |-> Y === 1'b0);

  // When B1 and C1 are 0, Y is the invert of A1&A2&A3
  assert property ((B1 === 1'b0 && C1 === 1'b0) |-> (Y === ~a_and));

  // No spurious glitches: if inputs are stable, output is stable
  assert property ($stable({A1,A2,A3,B1,C1}) |-> $stable(Y));

  // 4-state sanity: known inputs imply known output
  assert property (!$isunknown({A1,A2,A3,B1,C1}) |-> !$isunknown(Y));

  // Coverage: key corners and outcomes
  cover property (Y === 1'b1);
  cover property (Y === 1'b0);
  cover property (B1 === 1'b1 && Y === 1'b0);
  cover property (C1 === 1'b1 && Y === 1'b0);
  cover property (B1 === 1'b0 && C1 === 1'b0 && A1 === 1'b1 && A2 === 1'b1 && A3 === 1'b1 && Y === 1'b0);
  cover property (B1 === 1'b0 && C1 === 1'b0 && A1 === 1'b0 && A2 === 1'b0 && A3 === 1'b0 && Y === 1'b1);
endmodule

// Bind into the DUT
bind my_module my_module_sva sva_my_module (.*);