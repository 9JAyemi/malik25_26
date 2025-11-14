// SVA for power_check. Bind this to the DUT.

module power_check_sva (
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB,
  input logic power_ok
);
  // Sample on any edge of relevant signals
  default clocking cb @(
    posedge VPWR or negedge VPWR or
    posedge VPB  or negedge VPB  or
    posedge VGND or negedge VGND or
    posedge VNB  or negedge VNB  or
    posedge power_ok or negedge power_ok
  ); endclocking

  // Functional equivalence (4-state), allow delta for combinational update
  a_func_eq: assert property (1'b1 |-> ##0 (power_ok === (VPWR && VPB)));

  // Independence from unused pins: VGND/VNB must not affect power_ok
  a_independent_wells_gnd: assert property (
    ($changed({VGND,VNB}) && $stable({VPWR,VPB})) |-> ##0 $stable(power_ok)
  );

  // No spurious output toggle without VPWR/VPB toggle
  a_no_spurious_toggle: assert property (
    $changed(power_ok) |-> ($changed(VPWR) || $changed(VPB))
  );

  // Coverage: all input/output combos observed
  c_00: cover property (VPWR===0 && VPB===0 && power_ok===0);
  c_01: cover property (VPWR===0 && VPB===1 && power_ok===0);
  c_10: cover property (VPWR===1 && VPB===0 && power_ok===0);
  c_11: cover property (VPWR===1 && VPB===1 && power_ok===1);

  // Coverage: power_ok rises/falls appropriately
  c_rise: cover property ((VPWR==0 && VPB==0) ##1 (VPWR==1 && VPB==1) ##0 (power_ok==1));
  c_fall: cover property ((VPWR==1 && VPB==1) ##1 ((VPWR==0) || (VPB==0)) ##0 (power_ok==0));

  // Coverage: VGND/VNB toggles while VPWR/VPB stable do not change power_ok
  c_vgnd_indep: cover property (($changed(VGND) && $stable({VPWR,VPB})) ##0 $stable(power_ok));
  c_vnb_indep:  cover property (($changed(VNB)  && $stable({VPWR,VPB})) ##0 $stable(power_ok));
endmodule

bind power_check power_check_sva sva_inst (.VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB), .power_ok(power_ok));