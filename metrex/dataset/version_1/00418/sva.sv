// SVA checker for sky130_fd_sc_hd__o221a: X = (A1|A2) & (B1|B2) & C1
module sky130_fd_sc_hd__o221a_sva (
  input logic X,
  input logic A1, A2, B1, B2, C1
);
  logic exp;
  assign exp = (A1 | A2) & (B1 | B2) & C1;

  // Functional equivalence (4-state aware)
  ap_eq:     assert property (@(*)) (X === exp);

  // When inputs are known, output must be known and correct
  ap_known:  assert property (@(*)) (!$isunknown({A1,A2,B1,B2,C1})) |-> (!($isunknown(X)) && (X == exp));

  // Controlling value and corner checks
  ap_c0:     assert property (@(*)) (C1 === 1'b0) |-> ##0 (X === 1'b0);
  ap_a0:     assert property (@(*)) (C1 === 1'b1 && A1 === 1'b0 && A2 === 1'b0) |-> ##0 (X === 1'b0);
  ap_b0:     assert property (@(*)) (C1 === 1'b1 && B1 === 1'b0 && B2 === 1'b0) |-> ##0 (X === 1'b0);
  ap_all1:   assert property (@(*)) (C1 === 1'b1 && (A1|A2) === 1'b1 && (B1|B2) === 1'b1) |-> ##0 (X === 1'b1);

  // Coverage: all four minimal ways to get X=1
  cp_a1b1:   cover  property (@(*)) (C1 && A1 && !A2 && B1 && !B2 && X);
  cp_a1b2:   cover  property (@(*)) (C1 && A1 && !A2 && B2 && !B1 && X);
  cp_a2b1:   cover  property (@(*)) (C1 && A2 && !A1 && B1 && !B2 && X);
  cp_a2b2:   cover  property (@(*)) (C1 && A2 && !A1 && B2 && !B1 && X);

  // Coverage: X=0 due to each independent blocking reason
  cp_c0:     cover  property (@(*)) (!C1 && !X);
  cp_ag0:    cover  property (@(*)) (C1 && !A1 && !A2 && (B1 || B2) && !X);
  cp_bg0:    cover  property (@(*)) (C1 && !B1 && !B2 && (A1 || A2) && !X);
endmodule

bind sky130_fd_sc_hd__o221a sky130_fd_sc_hd__o221a_sva sva_i (
  .X(X), .A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1)
);