// SVA checker for mux4
module mux4_sva(
  input A0, A1, A2, A3, S0, S1, VPWR, VGND, VPB, VNB,
  input X
);
  // Derived expectations
  wire sel_a0 = ~S1 & ~S0;
  wire sel_a1 = ~S1 &  S0;
  wire sel_a2 =  S1 & ~S0;
  wire sel_a3 =  S1 &  S0;

  wire exp_w1 = sel_a0 ? A0 : sel_a1 ? A1 : sel_a2 ? A2 : A3;
  wire exp_w2 = (VGND == 1'b0) ? 1'b0 : VPWR;
  wire exp_w3 = (VPB  == 1'b0) ? 1'b0 : VNB;
  wire exp_X  = exp_w1 & exp_w2 & exp_w3;

  wire inputs_known = !$isunknown({A0,A1,A2,A3,S0,S1,VPWR,VGND,VPB,VNB});
  wire sel_known    = !$isunknown({S1,S0});
  wire power_on     = (VGND==1'b1 && VPWR==1'b1 && VPB==1'b1 && VNB==1'b1);

  // Sample on any input edge
  clocking cb @(
    posedge A0 or negedge A0 or
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge A3 or negedge A3 or
    posedge S0 or negedge S0 or
    posedge S1 or negedge S1 or
    posedge VPWR or negedge VPWR or
    posedge VGND or negedge VGND or
    posedge VPB or negedge VPB or
    posedge VNB or negedge VNB
  ); endclocking
  default clocking cb;

  // Core functional equivalence
  ap_func:        assert property (disable iff(!inputs_known) X == exp_X);

  // Select decoding sanity
  ap_onehot_sel:  assert property (disable iff(!sel_known) $onehot({sel_a0,sel_a1,sel_a2,sel_a3}));

  // Power gating effects
  ap_vgnd_kills:  assert property (disable iff($isunknown(VGND)) (VGND==1'b0) |-> (X==1'b0));
  ap_vpb_kills:   assert property (disable iff($isunknown(VPB))  (VPB ==1'b0) |-> (X==1'b0));
  ap_vpwr_zero:   assert property (disable iff($isunknown({VGND,VPWR})) ((VGND==1'b1)&&(VPWR==1'b0)) |-> (X==1'b0));
  ap_vnb_zero:    assert property (disable iff($isunknown({VPB,VNB}))   ((VPB ==1'b1)&&(VNB ==1'b0)) |-> (X==1'b0));

  // If X is high, all enables are high and selected input is high
  ap_x_high_imp:  assert property (disable iff(!inputs_known) X |-> (power_on && (exp_w1==1'b1)));

  // Coverage
  cp_power_on_sel0: cover property (power_on && sel_a0 && A0 && X);
  cp_power_on_sel1: cover property (power_on && sel_a1 && A1 && X);
  cp_power_on_sel2: cover property (power_on && sel_a2 && A2 && X);
  cp_power_on_sel3: cover property (power_on && sel_a3 && A3 && X);

  cp_vgnd_kill:     cover property ((VGND==1'b0) ##0 (X==1'b0));
  cp_vpb_kill:      cover property ((VPB ==1'b0) ##0 (X==1'b0));
  cp_vpwr_zero:     cover property ((VGND==1'b1 && VPWR==1'b0) ##0 (X==1'b0));
  cp_vnb_zero:      cover property ((VPB ==1'b1 && VNB ==1'b0) ##0 (X==1'b0));
endmodule

// Bind the checker to the DUT
bind mux4 mux4_sva mux4_sva_i(.*);