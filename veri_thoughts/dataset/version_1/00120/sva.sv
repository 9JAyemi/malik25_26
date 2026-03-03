// SVA for sky130_fd_sc_ms__a2111oi
// Concise, full functional check, power-aware, with focused coverage.

module sky130_fd_sc_ms__a2111oi_sva (
  input Y, A1, A2, B1, C1, D1, VPWR, VGND, VPB, VNB
);

  // Sample on any relevant edge to observe combinational updates
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge B1 or negedge B1 or
    posedge C1 or negedge C1 or
    posedge D1 or negedge D1 or
    posedge VPWR or negedge VPWR or
    posedge VGND or negedge VGND or
    posedge VPB  or negedge VPB  or
    posedge VNB  or negedge VNB
  ); endclocking

  // Power-good predicate (rails and wells correct)
  wire pwr_good = (VPWR === 1'b1) && (VGND === 1'b0) && (VPB === 1'b1) && (VNB === 1'b0);

  // Majority-of-three function for B1,C1,D1
  wire maj3 = (B1 & C1) | (B1 & D1) | (C1 & D1);

  // Core functional equivalence (evaluate in observed region via ##0)
  ap_func: assert property (pwr_good |-> ##0 (Y === maj3));

  // No X/Z on IO when powered
  ap_no_x:  assert property (pwr_good |-> ##0 (!$isunknown({A1,A2,B1,C1,D1,Y})));

  // Independence: A1, A2 must not affect Y (given stable B,C,D)
  ap_a1_indep: assert property (pwr_good && $changed(A1) && $stable({B1,C1,D1}) |-> ##0 $stable(Y));
  ap_a2_indep: assert property (pwr_good && $changed(A2) && $stable({B1,C1,D1}) |-> ##0 $stable(Y));

  // Optional: wells track rails when rails are valid
  ap_well_tie: assert property ((VPWR === 1'b1 && VGND === 1'b0) |-> ##0 (VPB === 1'b1 && VNB === 1'b0));

  // Coverage: exercise Y==1 for all majority cases and Y==0 for all minority cases
  cover property (pwr_good && ##0 (Y &&  ( B1 &&  C1 &&  D1)));
  cover property (pwr_good && ##0 (Y &&  ( B1 &&  C1 && !D1)));
  cover property (pwr_good && ##0 (Y &&  ( B1 && !C1 &&  D1)));
  cover property (pwr_good && ##0 (Y &&  (!B1 &&  C1 &&  D1)));

  cover property (pwr_good && ##0 (!Y && (!B1 && !C1 && !D1)));
  cover property (pwr_good && ##0 (!Y && ( B1 && !C1 && !D1)));
  cover property (pwr_good && ##0 (!Y && (!B1 &&  C1 && !D1)));
  cover property (pwr_good && ##0 (!Y && (!B1 && !C1 &&  D1)));

  // Coverage: show A1/A2 toggle without affecting Y (with stable B,C,D)
  cover property (pwr_good && $changed(A1) && $stable({B1,C1,D1}) ##0 $stable(Y));
  cover property (pwr_good && $changed(A2) && $stable({B1,C1,D1}) ##0 $stable(Y));

endmodule

// Bind into the DUT
bind sky130_fd_sc_ms__a2111oi sky130_fd_sc_ms__a2111oi_sva sva_i (.*);