// SVA checker bound into the DUT. Focused, 4‑state accurate, with concise coverage.

module OAI21B2HD4X_sva (
  input logic AN, BN, C,
  input logic Z,
  input logic I0_out, I1_out
);

  // Sample on any input edge to catch combinational updates; ##0 to allow delta-recompute.
  default clocking cb @(
    posedge AN or negedge AN or
    posedge BN or negedge BN or
    posedge C  or negedge C
  ); endclocking

  // Golden Boolean equivalence (4‑state)
  assert property (1 |-> ##0 (Z === ((~(AN & BN)) & C)))
    else $error("OAI21B2HD4X: Z != (~(AN & BN)) & C");

  // Gate-level chain consistency (4‑state)
  assert property (1 |-> ##0 (I0_out === (AN & BN)))
    else $error("OAI21B2HD4X: I0_out != AN & BN");
  assert property (1 |-> ##0 (I1_out === ~I0_out))
    else $error("OAI21B2HD4X: I1_out != ~I0_out");
  assert property (1 |-> ##0 (Z === (I1_out & C)))
    else $error("OAI21B2HD4X: Z != I1_out & C");

  // Known-when-inputs-known; and hard gating by C
  assert property ((!$isunknown({AN,BN,C})) |-> ##0 (!$isunknown(Z)))
    else $error("OAI21B2HD4X: Z is X/Z while inputs are known");
  assert property ((C === 1'b0) |-> ##0 (Z === 1'b0))
    else $error("OAI21B2HD4X: C=0 must force Z=0");
  assert property ((C===1'b1 && AN===1'b1 && BN===1'b1) |-> ##0 (Z===1'b0))
    else $error("OAI21B2HD4X: C=1, AN=1, BN=1 must yield Z=0");
  assert property ((C===1'b1 && (AN===1'b0 || BN===1'b0)) |-> ##0 (Z===1'b1))
    else $error("OAI21B2HD4X: C=1, any of AN/BN=0 must yield Z=1");

  // Functional coverage: all input combinations and both Z values
  cover property (AN==0 && BN==0 && C==0);
  cover property (AN==0 && BN==0 && C==1);
  cover property (AN==0 && BN==1 && C==0);
  cover property (AN==0 && BN==1 && C==1);
  cover property (AN==1 && BN==0 && C==0);
  cover property (AN==1 && BN==0 && C==1);
  cover property (AN==1 && BN==1 && C==0);
  cover property (AN==1 && BN==1 && C==1);

  cover property (Z==0);
  cover property (Z==1);

endmodule

bind OAI21B2HD4X OAI21B2HD4X_sva sva_i (
  .AN(AN), .BN(BN), .C(C), .Z(Z),
  .I0_out(I0_out), .I1_out(I1_out)
);