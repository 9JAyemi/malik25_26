// SVA for sky130_fd_sc_hd__and3b (X = B & C & ~A_N)
module sky130_fd_sc_hd__and3b_sva (
  input logic A_N, B, C, X,
  input logic VPWR, VGND, VPB, VNB
);

  // Functional correctness (when known)
  property p_func;
    @(A_N or B or C or X)
      !$isunknown({A_N,B,C,X}) |-> ##0 (X == ((~A_N) & B & C));
  endproperty
  assert property (p_func) else $error("and3b func: X != (~A_N & B & C)");

  // Dominating values
  assert property (@(A_N) (A_N===1'b1) |-> ##0 (X===1'b0))
    else $error("and3b A_N=1 should force X=0");
  assert property (@(B)   (B  ===1'b0) |-> ##0 (X===1'b0))
    else $error("and3b B=0 should force X=0");
  assert property (@(C)   (C  ===1'b0) |-> ##0 (X===1'b0))
    else $error("and3b C=0 should force X=0");
  assert property (@(A_N or B or C)
                   ((A_N===1'b0)&&(B===1'b1)&&(C===1'b1)) |-> ##0 (X===1'b1))
    else $error("and3b A_N=0,B=1,C=1 should force X=1");

  // No X/Z on X when inputs are known
  assert property (@(A_N or B or C or X)
                   !$isunknown({A_N,B,C}) |-> ##0 !$isunknown(X))
    else $error("and3b: X became X/Z with known inputs");

  // No spurious output toggle without input change
  assert property (@(A_N or B or C or X)
                   $changed(X) |-> $changed({A_N,B,C}))
    else $error("and3b: X toggled without input change");

  // Power/ground rails constant (triggers if they ever change)
  assert property (@(VPWR or VGND or VPB or VNB)
                   (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0))
    else $error("and3b: power/ground rails incorrect");

  // Coverage: all 8 input combinations, output pulse and both edges
  genvar i;
  for (i=0; i<8; i++) begin : g_cov_in
    localparam logic [2:0] V = i[2:0];
    cover property (@(A_N or B or C) {A_N,B,C}===V);
  end
  cover property (@(A_N or B or C or X) (A_N==0 && B==1 && C==1 && X==1));
  cover property (@(A_N or B or C or X) $rose(X));
  cover property (@(A_N or B or C or X) $fell(X));

endmodule

// Bind into the DUT
bind sky130_fd_sc_hd__and3b sky130_fd_sc_hd__and3b_sva u_and3b_sva (
  .A_N(A_N), .B(B), .C(C), .X(X),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);