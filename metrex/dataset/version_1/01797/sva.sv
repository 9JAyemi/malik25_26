// SVA checker for magnitude_comparator
module magnitude_comparator_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       EQ,
  input logic       GT,
  input logic       LT
);

  // Correctness vs spec; sample after combinational settle (##0)
  property p_compare_correct;
    @(A or B)
      1'b1 |-> ##0
        (!$isunknown({A,B}) |-> (
          (EQ === (A==B)) &&
          (GT === (A>B))  &&
          (LT === (A<B))
        ));
  endproperty
  assert property (p_compare_correct);

  // Known inputs -> exactly one outcome asserted
  property p_onehot_outcomes;
    @(A or B)
      1'b1 |-> ##0 (!$isunknown({A,B}) |-> $onehot({EQ,GT,LT}));
  endproperty
  assert property (p_onehot_outcomes);

  // Functional coverage of all three outcomes
  cover property (@(A or B) ##0 (!$isunknown({A,B}) && (A==B) &&  EQ && !GT && !LT));
  cover property (@(A or B) ##0 (!$isunknown({A,B}) && (A>B)  && !EQ &&  GT && !LT));
  cover property (@(A or B) ##0 (!$isunknown({A,B}) && (A<B)  && !EQ && !GT &&  LT));

endmodule

// Bind into the DUT
bind magnitude_comparator magnitude_comparator_sva u_magnitude_comparator_sva (
  .A(A), .B(B), .EQ(EQ), .GT(GT), .LT(LT)
);