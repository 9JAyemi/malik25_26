// SVA checker for sky130_fd_sc_lp__o221ai
module sky130_fd_sc_lp__o221ai_sva (
  input logic A1, A2, B1, B2, C1,
  input logic Y
);
  wire a_or  = A1 | A2;
  wire b_or  = B1 | B2;
  wire expY  = ~(C1 & a_or & b_or);

  // Functional equivalence (4-state accurate)
  assert property (@(A1 or A2 or B1 or B2 or C1 or Y) Y === expY);

  // Dominating conditions
  assert property (@(A1 or A2 or B1 or B2 or C1 or Y) (C1===1'b0) |-> (Y===1'b1));
  assert property (@(A1 or A2 or B1 or B2 or C1 or Y) ((A1===1'b0)&&(A2===1'b0)) |-> (Y===1'b1));
  assert property (@(A1 or A2 or B1 or B2 or C1 or Y) ((B1===1'b0)&&(B2===1'b0)) |-> (Y===1'b1));
  assert property (@(A1 or A2 or B1 or B2 or C1 or Y) (C1===1'b1 && a_or===1'b1 && b_or===1'b1) |-> (Y===1'b0));

  // Known-when-inputs-known
  assert property (@(A1 or A2 or B1 or B2 or C1 or Y) (!$isunknown({A1,A2,B1,B2,C1})) |-> !$isunknown(Y));

  // Coverage: Y both polarities
  cover property (@(A1 or A2 or B1 or B2 or C1 or Y) Y===1'b1);
  cover property (@(A1 or A2 or B1 or B2 or C1 or Y) Y===1'b0);

  // Coverage: all 8 combinations of (a_or, b_or, C1)
  cover property (@(A1 or A2 or B1 or B2 or C1) (a_or===1'b0 && b_or===1'b0 && C1===1'b0));
  cover property (@(A1 or A2 or B1 or B2 or C1) (a_or===1'b0 && b_or===1'b0 && C1===1'b1));
  cover property (@(A1 or A2 or B1 or B2 or C1) (a_or===1'b0 && b_or===1'b1 && C1===1'b0));
  cover property (@(A1 or A2 or B1 or B2 or C1) (a_or===1'b0 && b_or===1'b1 && C1===1'b1));
  cover property (@(A1 or A2 or B1 or B2 or C1) (a_or===1'b1 && b_or===1'b0 && C1===1'b0));
  cover property (@(A1 or A2 or B1 or B2 or C1) (a_or===1'b1 && b_or===1'b0 && C1===1'b1));
  cover property (@(A1 or A2 or B1 or B2 or C1) (a_or===1'b1 && b_or===1'b1 && C1===1'b0));
  cover property (@(A1 or A2 or B1 or B2 or C1) (a_or===1'b1 && b_or===1'b1 && C1===1'b1));

  // Y toggle coverage
  cover property (@(A1 or A2 or B1 or B2 or C1 or Y) $rose(Y));
  cover property (@(A1 or A2 or B1 or B2 or C1 or Y) $fell(Y));
endmodule

bind sky130_fd_sc_lp__o221ai sky130_fd_sc_lp__o221ai_sva sva_o221ai (.*);