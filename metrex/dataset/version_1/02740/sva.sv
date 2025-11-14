// SVA for my_module
module my_module_sva (
  input logic A1, A2, B1, C1, X,
  input logic and0_out, or0_out_X
);
  default clocking cb @(A1 or A2 or B1 or C1 or X or and0_out or or0_out_X); endclocking

  // Gate-level functional checks
  assert_and0_func: assert property (and0_out == (A1 & A2));
  assert_or0_func:  assert property (or0_out_X == (and0_out | C1 | B1));
  assert_buf_func:  assert property (X == or0_out_X);

  // End-to-end functional equivalence
  assert_end_to_end: assert property (X == ((A1 & A2) | C1 | B1));

  // Dominance and reverse implications
  assert_c1_dominates: assert property (C1 |-> X);
  assert_b1_dominates: assert property (B1 |-> X);
  assert_and_when_no_or: assert property ((C1==1'b0 && B1==1'b0 && A1 && A2) |-> X);
  assert_zero_backinf:  assert property (X==1'b0 |-> (C1==1'b0 && B1==1'b0 && (!A1 || !A2)));
  assert_high_backinf:  assert property ((X && !C1 && !B1) |-> (A1 && A2));

  // 4-state hygiene
  assert_known_when_inputs_known:
    assert property ((!$isunknown({A1,A2,B1,C1})) |-> (!$isunknown({and0_out,or0_out_X,X})));

  // Minimal coverage
  cover_rose_X:  cover property ($rose(X));
  cover_fell_X:  cover property ($fell(X));
  cover_via_C1:  cover property (C1 && !B1 && !(A1 && A2) && X);
  cover_via_B1:  cover property (B1 && !C1 && !(A1 && A2) && X);
  cover_via_AND: cover property (!C1 && !B1 && A1 && A2 && X);
  cover_X_low:   cover property (!C1 && !B1 && (!A1 || !A2) && !X);
endmodule

// Bind into DUT (checks internal nets too)
bind my_module my_module_sva sva_i (
  .A1(A1), .A2(A2), .B1(B1), .C1(C1), .X(X),
  .and0_out(and0_out), .or0_out_X(or0_out_X)
);