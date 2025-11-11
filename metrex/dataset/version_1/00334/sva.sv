// SVA for boolean_func
// Bind this checker to the DUT.
module boolean_func_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);
  // Local combine for B-path supplies
  wire bpath_en = VPWR & VGND & VPB & VNB;

  // Functional equivalence (sample after delta to avoid race with continuous assign)
  a_func_equiv: assert property (@(A1 or A2 or B1 or B2 or VPWR or VGND or VPB or VNB or X)
                                 ##0 X === ((A1 & A2) | (B1 & B2 & bpath_en)));

  // If inputs are known, output must be known
  a_known_out_when_known_in: assert property (@(A1 or A2 or B1 or B2 or VPWR or VGND or VPB or VNB or X)
                                              ##0 (!$isunknown({A1,A2,B1,B2,VPWR,VGND,VPB,VNB}))
                                                  |-> !$isunknown(X));

  // Minimal but meaningful functional coverage
  c_apath_only_high: cover property (@(A1 or A2 or B1 or B2 or VPWR or VGND or VPB or VNB or X)
                                     ##0 (A1 & A2) && !(B1 & B2 & bpath_en) && X);

  c_bpath_only_high: cover property (@(A1 or A2 or B1 or B2 or VPWR or VGND or VPB or VNB or X)
                                     ##0 (B1 & B2 & bpath_en) && !(A1 & A2) && X);

  c_both_paths_high: cover property (@(A1 or A2 or B1 or B2 or VPWR or VGND or VPB or VNB or X)
                                     ##0 (A1 & A2) && (B1 & B2 & bpath_en) && X);

  c_none_low: cover property (@(A1 or A2 or B1 or B2 or VPWR or VGND or VPB or VNB or X)
                              ##0 !(A1 & A2) && !(B1 & B2 & bpath_en) && !X);
endmodule

bind boolean_func boolean_func_sva u_boolean_func_sva (
  .A1(A1), .A2(A2), .B1(B1), .B2(B2),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
  .X(X)
);