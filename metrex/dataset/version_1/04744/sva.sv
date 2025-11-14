// SVA for logic_gate (4-input AND)
module logic_gate_sva (
  input  logic A1, A2, A3, B1,
  input  logic X
);
  // Helpers
  let AND4               = (A1 & A2 & A3 & B1);
  let all_known_inputs   = !$isunknown({A1,A2,A3,B1});
  let any_zero           = (A1===1'b0 || A2===1'b0 || A3===1'b0 || B1===1'b0);
  let no_zero            = !any_zero;

  // Functional equivalence (4-state aware) checked at end of timestep
  always_comb begin
    assert #0 (X === AND4)
      else $error("AND func mismatch: X=%b A1=%b A2=%b A3=%b B1=%b", X,A1,A2,A3,B1);

    if (all_known_inputs)
      assert #0 (!$isunknown(X))
        else $error("X is X/Z while all inputs are known: A1=%b A2=%b A3=%b B1=%b", A1,A2,A3,B1);
  end

  // Optional dominance check (redundant with equivalence but diagnostic-friendly)
  property zero_dominance;
    @(A1 or A2 or A3 or B1) any_zero |-> (X===1'b0);
  endproperty
  assert property (zero_dominance);

  // Coverage: reachability and X-propagation
  cover property (@(A1 or A2 or A3 or B1) (A1===1 && A2===1 && A3===1 && B1===1 && X===1)); // all-ones -> X=1
  cover property (@(A1 or A2 or A3 or B1) (A1===0 && A2===1 && A3===1 && B1===1 && X===0));
  cover property (@(A1 or A2 or A3 or B1) (A2===0 && A1===1 && A3===1 && B1===1 && X===0));
  cover property (@(A1 or A2 or A3 or B1) (A3===0 && A1===1 && A2===1 && B1===1 && X===0));
  cover property (@(A1 or A2 or A3 or B1) (B1===0 && A1===1 && A2===1 && A3===1 && X===0));

  // X propagates when no input is known-0 and at least one input is X/Z
  cover property (@(A1 or A2 or A3 or B1) (no_zero && $isunknown({A1,A2,A3,B1}) && $isunknown(X)));

  // Known-0 masks unknowns
  cover property (@(A1 or A2 or A3 or B1) (any_zero && $isunknown({A1,A2,A3,B1}) && X===0));
endmodule

bind logic_gate logic_gate_sva sva_inst (.*);