// SVA for power_module
module power_module_sva (
  input logic VPB, VPWR, VGND, VNB,
  input logic HI, LO
);

  // Sample on any input change
  clocking cb @(
    posedge VPB or negedge VPB or
    posedge VPWR or negedge VPWR or
    posedge VGND or negedge VGND or
    posedge VNB or negedge VNB
  ); endclocking
  default clocking cb;

  // Derived conditions (sampled)
  wire c1 = VPB;
  wire c2 = VPWR && !VGND;
  wire c3 = VNB;
  wire c4 = !VPWR && VGND;

  // Basic encoding checks
  a_no_both_hi_lo:      assert property (!(HI && LO));
  a_valid_states_only:  assert property ((HI && !LO) || (!HI && LO) || (!HI && !LO));
  a_no_x_out:           assert property (!$isunknown({HI, LO}));

  // Functional equivalence of priority logic
  a_hi_func: assert property (HI == (c1 || c2));
  a_lo_func: assert property (LO == ((!(c1 || c2)) && (c3 || c4)));

  // Priority mask: when HI drivers active, LO must be 0 even if LO drivers request it
  a_lo_masked_when_hi: assert property (((c3 || c4) && (c1 || c2)) |-> !LO);

  // Full branch coverage
  c_hi_by_vpb:       cover property ( c1                              &&  HI && !LO);
  c_hi_by_vpwr:      cover property (!c1 &&  c2                       &&  HI && !LO);
  c_lo_by_vnb:       cover property (!(c1||c2) &&  c3                 && !HI &&  LO);
  c_lo_by_rails:     cover property (!(c1||c2||c3) &&  c4             && !HI &&  LO);
  c_default_zero:    cover property (!(c1||c2||c3||c4)                && !HI && !LO);

  // Overlap/priority scenarios
  c_vpb_over_vnb:    cover property ( c1 &&  c3 &&                    HI && !LO);
  c_vpwr_over_vnb:   cover property ( c2 &&  c3 &&                    HI && !LO);

endmodule

// Bind into DUT
bind power_module power_module_sva sva (
  .VPB(VPB), .VPWR(VPWR), .VGND(VGND), .VNB(VNB),
  .HI(HI), .LO(LO)
);