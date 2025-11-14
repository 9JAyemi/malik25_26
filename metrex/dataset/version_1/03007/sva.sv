// SVA checker for my_logic
module my_logic_sva (
  input logic A1_N,
  input logic A2_N,
  input logic B1,
  input logic B2,
  input logic X
);

  // Helper expression (when inputs known)
  function automatic logic x_expr(input logic A1_N, A2_N, B1, B2);
    return (A1_N & ~A2_N & B1  & ~B2) |
           (A2_N & ~A1_N & ~B1 &  B2);
  endfunction

  // No X/Z on inputs
  ap_no_x_inputs: assert property (@(A1_N or A2_N or B1 or B2)
    !$isunknown({A1_N,A2_N,B1,B2}));

  // No X/Z on X when inputs are known
  ap_no_x_out: assert property (@(A1_N or A2_N or B1 or B2 or X)
    !$isunknown({A1_N,A2_N,B1,B2}) |-> ##0 !$isunknown(X));

  // Functional equivalence (concise truth table)
  ap_func: assert property (@(A1_N or A2_N or B1 or B2 or X)
    !$isunknown({A1_N,A2_N,B1,B2}) |-> ##0 (X == x_expr(A1_N,A2_N,B1,B2)));

  // Quadrant checks
  ap_q11_zero: assert property (@(A1_N or A2_N or B1 or B2)
    (!$isunknown({A1_N,A2_N,B1,B2}) &&  A1_N &&  A2_N) |-> ##0 (X == 1'b0));

  ap_q00_zero: assert property (@(A1_N or A2_N or B1 or B2)
    (!$isunknown({A1_N,A2_N,B1,B2}) && !A1_N && !A2_N) |-> ##0 (X == 1'b0));

  ap_q10_eq: assert property (@(A1_N or A2_N or B1 or B2)
    (!$isunknown({A1_N,A2_N,B1,B2}) &&  A1_N && !A2_N) |-> ##0 (X == (B1 && !B2)));

  ap_q01_eq: assert property (@(A1_N or A2_N or B1 or B2)
    (!$isunknown({A1_N,A2_N,B1,B2}) && !A1_N &&  A2_N) |-> ##0 (X == (!B1 && B2)));

  // Mutual exclusivity of the two 1-implicants
  ap_me_ones: assert property (@(A1_N or A2_N or B1 or B2)
    !((A1_N && !A2_N && B1 && !B2) && (A2_N && !A1_N && !B1 && B2)));

  // Coverage: both 1-cases
  cp_x1_case1: cover property (@(A1_N or A2_N or B1 or B2)
    !$isunknown({A1_N,A2_N,B1,B2}) &&  A1_N && !A2_N &&  B1 && !B2 && ##0 X);

  cp_x1_case2: cover property (@(A1_N or A2_N or B1 or B2)
    !$isunknown({A1_N,A2_N,B1,B2}) && !A1_N &&  A2_N && !B1 &&  B2 && ##0 X);

  // Coverage: both equal-quadrants produce 0
  cp_q11_zero: cover property (@(A1_N or A2_N or B1 or B2)
    !$isunknown({A1_N,A2_N,B1,B2}) && A1_N && A2_N && ##0 !X);

  cp_q00_zero: cover property (@(A1_N or A2_N or B1 or B2)
    !$isunknown({A1_N,A2_N,B1,B2}) && !A1_N && !A2_N && ##0 !X);

  // Coverage: the 0-cases in the asymmetric quadrants
  cp_q10_zero_else: cover property (@(A1_N or A2_N or B1 or B2)
    !$isunknown({A1_N,A2_N,B1,B2}) &&  A1_N && !A2_N && (!B1 || B2) && ##0 !X);

  cp_q01_zero_else: cover property (@(A1_N or A2_N or B1 or B2)
    !$isunknown({A1_N,A2_N,B1,B2}) && !A1_N &&  A2_N && ( B1 || !B2) && ##0 !X);

endmodule

// Bind into the DUT
bind my_logic my_logic_sva my_logic_sva_i (.*);