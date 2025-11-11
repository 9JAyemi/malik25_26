// SVA for max_value (bindable, combinational-safe using ##0)
module max_value_sva (
  input [7:0] a,
  input [7:0] b,
  input [7:0] max,
  input       equal_flag
);

  // Functional correctness
  property p_max_correct;
    @(a or b) disable iff ($isunknown({a,b}))
      1 |-> ##0 (max == ((a>=b) ? a : b));
  endproperty
  assert property (p_max_correct);

  property p_eqflag_correct;
    @(a or b) disable iff ($isunknown({a,b}))
      1 |-> ##0 (equal_flag == (a == b));
  endproperty
  assert property (p_eqflag_correct);

  // Max must be one of the inputs
  assert property (@(a or b) disable iff ($isunknown({a,b}))
      1 |-> ##0 (max == a || max == b));

  // Outputs are known when inputs are known
  assert property (@(a or b)
      !$isunknown({a,b}) |-> ##0 !$isunknown({max, equal_flag}));

  // Tie-case consistency
  assert property (@(a or b) disable iff ($isunknown({a,b}))
      (a==b) |-> ##0 (equal_flag && max==a && max==b));

  // Functional coverage of all branches
  cover property (@(a or b) (a>b)  ##0 (max==a && !equal_flag));
  cover property (@(a or b) (b>a)  ##0 (max==b && !equal_flag));
  cover property (@(a or b) (a==b) ##0 (max==a &&  equal_flag));

endmodule

bind max_value max_value_sva sva_i (.a(a), .b(b), .max(max), .equal_flag(equal_flag));