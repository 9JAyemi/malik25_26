// SVA for sky130_fd_sc_hdll__nand3b
// Function: Y = ~(B & ~A_N & C)

module sky130_fd_sc_hdll__nand3b_sva (input logic Y, A_N, B, C);

  // Sample on any input/output activity; use ##0 to avoid race with 0-delay logic
  default clocking cb @(A_N or B or C or Y); endclocking

  // Functional equivalence (4-state accurate)
  ap_func_4state: assert property (##0 (Y === ~(B & ~A_N & C)));

  // When inputs are known, output must be known and match the boolean function
  ap_known: assert property (
    !$isunknown({A_N,B,C}) |-> ##0 (! $isunknown(Y) && (Y == ~(B & ~A_N & C)))
  );

  // Controlling value checks
  ap_AN1 : assert property ((A_N === 1'b1)                          |-> ##0 (Y === 1'b1));
  ap_B0  : assert property ((B   === 1'b0)                          |-> ##0 (Y === 1'b1));
  ap_C0  : assert property ((C   === 1'b0)                          |-> ##0 (Y === 1'b1));
  ap_all1: assert property ((A_N === 1'b0 && B === 1'b1 && C === 1'b1) |-> ##0 (Y === 1'b0));

  // No spontaneous output changes without input activity
  ap_no_spurious_toggle: assert property ($stable({A_N,B,C}) |-> $stable(Y));

  // Coverage: exercise all input combinations
  c_000: cover property (A_N==0 && B==0 && C==0);
  c_001: cover property (A_N==0 && B==0 && C==1);
  c_010: cover property (A_N==0 && B==1 && C==0);
  c_011: cover property (A_N==0 && B==1 && C==1);
  c_100: cover property (A_N==1 && B==0 && C==0);
  c_101: cover property (A_N==1 && B==0 && C==1);
  c_110: cover property (A_N==1 && B==1 && C==0);
  c_111: cover property (A_N==1 && B==1 && C==1);

  // Coverage: observe both output levels and edges
  c_y0: cover property (Y==0);
  c_y1: cover property (Y==1);
  c_rise: cover property (@(posedge Y) 1);
  c_fall: cover property (@(negedge Y) 1);

endmodule

bind sky130_fd_sc_hdll__nand3b sky130_fd_sc_hdll__nand3b_sva u_nand3b_sva (.*);