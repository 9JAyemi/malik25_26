// SVA for majority_3. Bind this checker to the DUT.
checker majority_3_sva (input logic A, B, C, X, AB, AC, BC);

  // Sanity: no X/Z on primary I/Os
  ap_no_x: assert property (@(A or B or C or X) !$isunknown({A,B,C,X}));

  // Internal nets are correct
  ap_int_ands: assert property (@(A or B or C) ##0
                                (AB == (A & B) && AC == (A & C) && BC == (B & C)));

  // Functional majority relation
  ap_majority: assert property (@(A or B or C) ##0
                                (X == ((A & B) | (A & C) | (B & C))));

  // Full input-space coverage (expects correct X)
  cp_000: cover property (@(A or B or C) ##0 ({A,B,C} == 3'b000 && X == 1'b0));
  cp_001: cover property (@(A or B or C) ##0 ({A,B,C} == 3'b001 && X == 1'b0));
  cp_010: cover property (@(A or B or C) ##0 ({A,B,C} == 3'b010 && X == 1'b0));
  cp_011: cover property (@(A or B or C) ##0 ({A,B,C} == 3'b011 && X == 1'b1));
  cp_100: cover property (@(A or B or C) ##0 ({A,B,C} == 3'b100 && X == 1'b0));
  cp_101: cover property (@(A or B or C) ##0 ({A,B,C} == 3'b101 && X == 1'b1));
  cp_110: cover property (@(A or B or C) ##0 ({A,B,C} == 3'b110 && X == 1'b1));
  cp_111: cover property (@(A or B or C) ##0 ({A,B,C} == 3'b111 && X == 1'b1));

endchecker

bind majority_3 majority_3_sva chk (
  .A(A), .B(B), .C(C), .X(X),
  .AB(AB), .AC(AC), .BC(BC)
);