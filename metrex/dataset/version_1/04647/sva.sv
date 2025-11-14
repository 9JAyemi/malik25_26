// SVA for sky130_fd_sc_hdll__nor3 (3-input NOR with buf)
module sky130_fd_sc_hdll__nor3_sva (input logic A, B, C, Y);
  // Sample on any edge of inputs or output
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C or
    posedge Y or negedge Y
  ); endclocking

  // Functional equivalence (4-state accurate, zero-delay)
  a_func: assert property (1'b1 |=> (Y === ~(A | B | C)));

  // Deterministic cases
  a_any1_forces0: assert property ((A===1 || B===1 || C===1) |=> (Y===1'b0));
  a_all0_forces1: assert property ((A===0 && B===0 && C===0) |=> (Y===1'b1));

  // No X on output when inputs are known
  a_known_out_when_known_in: assert property (!$isunknown({A,B,C}) |=> !$isunknown(Y));

  // No spurious output change without input change
  a_no_spurious_y: assert property ($changed(Y) |-> ($changed(A) or $changed(B) or $changed(C)));

  // Coverage: all input combinations with correct Y
  c_000: cover property (A==0 && B==0 && C==0 && Y==1);
  c_001: cover property (A==0 && B==0 && C==1 && Y==0);
  c_010: cover property (A==0 && B==1 && C==0 && Y==0);
  c_011: cover property (A==0 && B==1 && C==1 && Y==0);
  c_100: cover property (A==1 && B==0 && C==0 && Y==0);
  c_101: cover property (A==1 && B==0 && C==1 && Y==0);
  c_110: cover property (A==1 && B==1 && C==0 && Y==0);
  c_111: cover property (A==1 && B==1 && C==1 && Y==0);

  // Coverage: output toggling
  c_y_rise: cover property ($rose(Y));
  c_y_fall: cover property ($fell(Y));
endmodule

bind sky130_fd_sc_hdll__nor3 sky130_fd_sc_hdll__nor3_sva sva(.A(A), .B(B), .C(C), .Y(Y));