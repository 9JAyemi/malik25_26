// SVA checker for sky130_fd_sc_lp__nor3b
// Function: Y = C_N & ~(A | B)

module sky130_fd_sc_lp__nor3b_sva
(
  input logic Y,
  input logic A,
  input logic B,
  input logic C_N,

  // internal nodes (for structural checks)
  input logic nor0_out,
  input logic and0_out_Y
);

  // Functional equivalence (4-state)
  assert property (@(A or B or C_N or Y) 1 |-> ##0 (Y === (C_N & ~(A | B))));

  // Structural consistency
  assert property (@(A or B or C_N or Y) 1 |-> ##0 (nor0_out    === ~(A | B)));
  assert property (@(A or B or C_N or Y) 1 |-> ##0 (and0_out_Y  === (C_N & nor0_out)));
  assert property (@(A or B or C_N or Y) 1 |-> ##0 (Y           === and0_out_Y));

  // Dominance / determinism (robust to Xs on other inputs)
  assert property (@(A or B or C_N or Y) A         |-> ##0 (Y == 1'b0));
  assert property (@(A or B or C_N or Y) B         |-> ##0 (Y == 1'b0));
  assert property (@(A or B or C_N or Y) !C_N      |-> ##0 (Y == 1'b0));
  assert property (@(A or B or C_N or Y) ( C_N && !A && !B) |-> ##0 (Y == 1'b1));
  assert property (@(A or B or C_N or Y) (Y === 1'b1)       |-> ##0 ( C_N && !A && !B));

  // Input space coverage (all 8 combinations)
  cover property (@(A or B or C_N) ##0 (A==0 && B==0 && C_N==0));
  cover property (@(A or B or C_N) ##0 (A==0 && B==0 && C_N==1));
  cover property (@(A or B or C_N) ##0 (A==0 && B==1 && C_N==0));
  cover property (@(A or B or C_N) ##0 (A==0 && B==1 && C_N==1));
  cover property (@(A or B or C_N) ##0 (A==1 && B==0 && C_N==0));
  cover property (@(A or B or C_N) ##0 (A==1 && B==0 && C_N==1));
  cover property (@(A or B or C_N) ##0 (A==1 && B==1 && C_N==0));
  cover property (@(A or B or C_N) ##0 (A==1 && B==1 && C_N==1));

  // Output activity coverage
  cover property (@(A or B or C_N or Y) $rose(Y));
  cover property (@(A or B or C_N or Y) $fell(Y));

endmodule

// Bind into DUT; explicit connections include internal nets
bind sky130_fd_sc_lp__nor3b sky130_fd_sc_lp__nor3b_sva
  i_sky130_fd_sc_lp__nor3b_sva (
    .Y(Y), .A(A), .B(B), .C_N(C_N),
    .nor0_out(nor0_out), .and0_out_Y(and0_out_Y)
  );