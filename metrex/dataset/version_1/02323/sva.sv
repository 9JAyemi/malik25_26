// SVA for sky130_fd_sc_hvl__a21oi (Y = ~(B1 | (A1 & A2)))
// Bind into the DUT to access internal nets and supplies.

module sva_sky130_fd_sc_hvl__a21oi;

  // Evaluate on any combinational activity
  default clocking cb @(A1 or A2 or B1 or and0_out or nor0_out_Y or Y); endclocking

  // Power/ground rails must be at expected constants
  assert property (VPWR === 1'b1 && VPB === 1'b1 && VGND === 1'b0 && VNB === 1'b0);

  // Functional equivalence (4-state clean)
  assert property (Y === ~(B1 | (A1 & A2)));

  // Internal net consistency
  assert property (and0_out   === (A1 & A2));
  assert property (nor0_out_Y === ~(B1 | and0_out));
  assert property (Y          === nor0_out_Y);

  // Deterministic output under partial Xs (dominance checks)
  assert property (B1 === 1'b1 |-> Y === 1'b0);
  assert property (B1 === 1'b0 && A1 === 1'b1 && A2 === 1'b1 |-> Y === 1'b0);
  assert property (B1 === 1'b0 && (A1 === 1'b0 || A2 === 1'b0) |-> Y === 1'b1);

  // No X on Y when inputs are known
  assert property (!$isunknown({A1,A2,B1}) |-> !$isunknown(Y));

  // Stability: with inputs stable, output must be stable
  assert property ($stable({A1,A2,B1}) |-> $stable(Y));

  // Truth-table coverage (all 8 input combinations with expected Y)
  cover property (A1==0 && A2==0 && B1==0 ##0 (Y==1));
  cover property (A1==0 && A2==0 && B1==1 ##0 (Y==0));
  cover property (A1==0 && A2==1 && B1==0 ##0 (Y==1));
  cover property (A1==0 && A2==1 && B1==1 ##0 (Y==0));
  cover property (A1==1 && A2==0 && B1==0 ##0 (Y==1));
  cover property (A1==1 && A2==0 && B1==1 ##0 (Y==0));
  cover property (A1==1 && A2==1 && B1==0 ##0 (Y==0));
  cover property (A1==1 && A2==1 && B1==1 ##0 (Y==0));

  // Toggle coverage
  cover property ($rose(Y));  cover property ($fell(Y));
  cover property ($rose(A1)); cover property ($rose(A2)); cover property ($rose(B1));

endmodule

bind sky130_fd_sc_hvl__a21oi sva_sky130_fd_sc_hvl__a21oi sva_a21oi_i();