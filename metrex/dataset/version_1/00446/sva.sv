// SVA for diode_module
// Bind these assertions to the DUT

module diode_module_sva (
    input        DIODE,
    input  signed [4:0] VPWR,
    input  signed [4:0] VGND,
    input  signed [4:0] VPB,
    input  signed [4:0] VNB,
    input  signed [4:0] VOUT
);

  // Sample on the global clock (works for combinational checks)
  default clocking cb @($global_clock); endclocking

  // Functional equivalence (bit-accurate, including X/Z semantics)
  a_func: assert property (
    VOUT === ((DIODE == 1'b1) ? ($signed(VPB) - $signed(VNB)) : 5'sd0)
  );

  // DIODE should be 2-state for deterministic behavior
  a_diode_2state: assert property (DIODE inside {1'b0, 1'b1});

  // If only VPWR/VGND change (and DIODE/VPB/VNB are stable), VOUT must remain stable
  a_power_indep: assert property (
    !((($changed(VPWR) || $changed(VGND)) && $stable({DIODE,VPB,VNB})) && !$stable(VOUT))
  );

  // VOUT must not change unless DIODE/VPB/VNB changed
  a_vout_change_cause: assert property (
    !($changed(VOUT) && $stable({DIODE,VPB,VNB}))
  );

  // No X/Z on VOUT when driving inputs are 2-state
  a_no_x_vout_when_clean: assert property (
    (!$isunknown({DIODE,VPB,VNB})) |-> !$isunknown(VOUT)
  );

  // Coverage
  c_diode0:       cover property (DIODE == 1'b0 && VOUT == 5'sd0);
  c_diode1_pos:   cover property (DIODE == 1'b1 && VOUT >  5'sd0);
  c_diode1_neg:   cover property (DIODE == 1'b1 && VOUT <  5'sd0);
  c_diode1_zero:  cover property (DIODE == 1'b1 && VOUT == 5'sd0);
  c_max_pos:      cover property (DIODE == 1'b1 && VOUT == 5'sd15);
  c_min_neg:      cover property (DIODE == 1'b1 && VOUT == 5'sd-16);
  c_rose_diode:   cover property ($rose(DIODE));
  c_fall_diode:   cover property ($fell(DIODE));

endmodule

bind diode_module diode_module_sva u_diode_module_sva (
  .DIODE(DIODE),
  .VPWR (VPWR),
  .VGND (VGND),
  .VPB  (VPB),
  .VNB  (VNB),
  .VOUT (VOUT)
);