// SVA for or3 — concise, high-quality checks and coverage
// Bind this checker to the DUT
module or3_sva (
  input A, B, C, X,
  input VPB, VPWR, VGND, VNB
);
  // Helper logic
  wire supplies_known = !$isunknown({VPWR,VGND,VPB,VNB});
  wire body_tied      = (VPB === VPWR) && (VNB === VGND);
  wire power_good     = (VPWR === 1'b1) && (VGND === 1'b0) && body_tied;

  // Functional correctness when powered and inputs known
  property p_func_or3;
    @(A or B or C or X or VPWR or VGND or VPB or VNB)
      power_good && !$isunknown({A,B,C}) |-> (X === (A | B | C));
  endproperty
  assert property(p_func_or3);

  // No spurious output toggles when inputs and supplies are stable
  property p_no_spurious_out;
    @(A or B or C or X or VPWR or VGND)
      power_good && $stable({A,B,C,VPWR,VGND}) |-> $stable(X);
  endproperty
  assert property(p_no_spurious_out);

  // Body ties must match supplies when all known
  property p_body_tied_to_supplies;
    @(VPB or VNB or VPWR or VGND)
      supplies_known |-> body_tied;
  endproperty
  assert property(p_body_tied_to_supplies);

  // Basic power-good coverage
  cover property (@(VPWR or VGND or VPB or VNB) power_good);
  cover property (@(VPWR or VGND or VPB or VNB) !power_good);

  // Truth-table coverage under power_good
  cover property (@(A or B or C or X or VPWR or VGND)
                  power_good && A==1'b0 && B==1'b0 && C==1'b0 && X==1'b0);
  cover property (@(A or B or C or X or VPWR or VGND)
                  power_good && A==1'b1 && B==1'b0 && C==1'b0 && X==1'b1);
  cover property (@(A or B or C or X or VPWR or VGND)
                  power_good && A==1'b0 && B==1'b1 && C==1'b0 && X==1'b1);
  cover property (@(A or B or C or X or VPWR or VGND)
                  power_good && A==1'b0 && B==1'b0 && C==1'b1 && X==1'b1);
  cover property (@(A or B or C or X or VPWR or VGND)
                  power_good && A==1'b1 && B==1'b1 && C==1'b0 && X==1'b1);
  cover property (@(A or B or C or X or VPWR or VGND)
                  power_good && A==1'b1 && B==1'b0 && C==1'b1 && X==1'b1);
  cover property (@(A or B or C or X or VPWR or VGND)
                  power_good && A==1'b0 && B==1'b1 && C==1'b1 && X==1'b1);
  cover property (@(A or B or C or X or VPWR or VGND)
                  power_good && A==1'b1 && B==1'b1 && C==1'b1 && X==1'b1);

  // Output transition coverage under power_good
  cover property (@(A or B or C or X or VPWR or VGND) power_good && $rose(X));
  cover property (@(A or B or C or X or VPWR or VGND) power_good && $fell(X));
endmodule

// Bind to DUT
bind or3 or3_sva u_or3_sva(.A(A), .B(B), .C(C), .X(X), .VPB(VPB), .VPWR(VPWR), .VGND(VGND), .VNB(VNB));