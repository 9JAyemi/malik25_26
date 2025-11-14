// SVA for sky130_fd_sc_hdll__nand3b
// Function: Y = ~(B & ~A_N & C)
module sky130_fd_sc_hdll__nand3b_sva
(
  input logic Y,
  input logic A_N,
  input logic B,
  input logic C,
  input logic not0_out,
  input logic nand0_out_Y
);
  default clocking cb @(A_N or B or C or Y or not0_out or nand0_out_Y); endclocking

  // Functional equivalence (allow settle in ##0)
  assert property (1'b1 |-> ##0 (Y === ~(B & ~A_N & C)));

  // Internal structure checks
  assert property (1'b1 |-> ##0 (not0_out    === ~A_N));
  assert property (1'b1 |-> ##0 (nand0_out_Y === ~(B & not0_out & C)));
  assert property (1'b1 |-> ##0 (Y === nand0_out_Y));

  // Controlling-value invariants
  assert property ((B == 1'b0) |-> ##0 (Y == 1'b1));
  assert property ((C == 1'b0) |-> ##0 (Y == 1'b1));
  assert property (((B == 1'b1) && (C == 1'b1)) |-> ##0 (Y === A_N));
  assert property ((A_N == 1'b1) |-> ##0 (Y == 1'b1));

  // No X/Z on Y when inputs are known
  assert property ((!$isunknown({A_N,B,C})) |-> ##0 (!$isunknown(Y)));

  // Output changes only due to input changes
  assert property (@(A_N or B or C or Y) $changed(Y) |-> ($changed(A_N) || $changed(B) || $changed(C)));

  // Truth-table coverage (all 8 input combinations)
  cover property (@(A_N or B or C) ##0 (A_N==0 && B==0 && C==0 && Y===1));
  cover property (@(A_N or B or C) ##0 (A_N==0 && B==0 && C==1 && Y===1));
  cover property (@(A_N or B or C) ##0 (A_N==0 && B==1 && C==0 && Y===1));
  cover property (@(A_N or B or C) ##0 (A_N==0 && B==1 && C==1 && Y===0)); // only 0 case
  cover property (@(A_N or B or C) ##0 (A_N==1 && B==0 && C==0 && Y===1));
  cover property (@(A_N or B or C) ##0 (A_N==1 && B==0 && C==1 && Y===1));
  cover property (@(A_N or B or C) ##0 (A_N==1 && B==1 && C==0 && Y===1));
  cover property (@(A_N or B or C) ##0 (A_N==1 && B==1 && C==1 && Y===1));

  // Y toggle coverage
  cover property (@(A_N or B or C or Y) $rose(Y));
  cover property (@(A_N or B or C or Y) $fell(Y));
endmodule

bind sky130_fd_sc_hdll__nand3b sky130_fd_sc_hdll__nand3b_sva
  sva_i (.Y(Y), .A_N(A_N), .B(B), .C(C), .not0_out(not0_out), .nand0_out_Y(nand0_out_Y));