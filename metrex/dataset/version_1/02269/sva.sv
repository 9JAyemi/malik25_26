// SVA for ddr_interface
// Focus: counter increment/wrap, output mapping, basic clock sanity, and concise coverage

bind ddr_interface ddr_interface_assertions ddr_interface_assertions_i (
  .FIXED_IO_ps_clk(FIXED_IO_ps_clk),
  .PL_SGMII_REFCLK_125M_P(PL_SGMII_REFCLK_125M_P),
  .PL_SGMII_REFCLK_125M_N(PL_SGMII_REFCLK_125M_N),
  .cnt_0(cnt_0), .cnt_1(cnt_1), .cnt_2(cnt_2), .cnt_3(cnt_3),
  .pl_led(pl_led), .pl_pmod(pl_pmod)
);

module ddr_interface_assertions (
  input  logic              FIXED_IO_ps_clk,
  input  logic              PL_SGMII_REFCLK_125M_P,
  input  logic              PL_SGMII_REFCLK_125M_N,
  input  logic [23:0]       cnt_0,
  input  logic [24:0]       cnt_1,
  input  logic [24:0]       cnt_2,
  input  logic [23:0]       cnt_3,
  input  logic [1:0]        pl_led,
  input  logic [1:0]        pl_pmod
);

  // Clocking blocks with #1step input skew to avoid NBA race on sampled signals
  clocking cb_ps @(posedge FIXED_IO_ps_clk);
    default input #1step output #0;
    input cnt_0, cnt_1, cnt_2, pl_led, pl_pmod;
  endclocking

  clocking cb_sgmii @(posedge PL_SGMII_REFCLK_125M_P);
    default input #1step output #0;
    input cnt_3, pl_pmod;
  endclocking

  // Wrap values
  localparam int unsigned CNT0_WRAP = 24'd8388607;   // 2^23-1
  localparam int unsigned CNT1_WRAP = 25'd16777215;  // 2^24-1
  localparam int unsigned CNT2_WRAP = 25'd33554431;  // 2^25-1
  localparam int unsigned CNT3_WRAP = 24'd16777215;  // 2^24-1

  // Counters increment or wrap exactly as coded
  ap_cnt0_inc_wrap: assert property (@cb_ps
    !$isunknown($past(cb_ps.cnt_0)) |-> cb_ps.cnt_0 == (($past(cb_ps.cnt_0)==CNT0_WRAP) ? 24'd0 : $past(cb_ps.cnt_0)+1)
  );

  ap_cnt1_inc_wrap: assert property (@cb_ps
    !$isunknown($past(cb_ps.cnt_1)) |-> cb_ps.cnt_1 == (($past(cb_ps.cnt_1)==CNT1_WRAP) ? 25'd0 : $past(cb_ps.cnt_1)+1)
  );

  ap_cnt2_inc_wrap: assert property (@cb_ps
    !$isunknown($past(cb_ps.cnt_2)) |-> cb_ps.cnt_2 == (($past(cb_ps.cnt_2)==CNT2_WRAP) ? 25'd0 : $past(cb_ps.cnt_2)+1)
  );

  ap_cnt3_inc_wrap: assert property (@cb_sgmii
    !$isunknown($past(cb_sgmii.cnt_3)) |-> cb_sgmii.cnt_3 == (($past(cb_sgmii.cnt_3)==CNT3_WRAP) ? 24'd0 : $past(cb_sgmii.cnt_3)+1)
  );

  // Outputs are known
  ap_led_known:  assert property (@cb_ps !$isunknown(cb_ps.pl_led));
  ap_pmod_known: assert property (@cb_ps !$isunknown(cb_ps.pl_pmod));

  // Output mapping to counter MSBs (sampled after NBA)
  ap_led0_map:  assert property (@cb_ps (!$isunknown({cb_ps.cnt_0,cb_ps.pl_led[0]})) |-> cb_ps.pl_led[0]  == cb_ps.cnt_0[23]);
  ap_led1_map:  assert property (@cb_ps (!$isunknown({cb_ps.cnt_1,cb_ps.pl_led[1]})) |-> cb_ps.pl_led[1]  == cb_ps.cnt_1[24]);
  ap_pmod0_map: assert property (@cb_ps (!$isunknown({cb_ps.cnt_2,cb_ps.pl_pmod[0]})) |-> cb_ps.pl_pmod[0] == cb_ps.cnt_2[24]);
  ap_pmod1_map: assert property (@cb_sgmii (!$isunknown({cb_sgmii.cnt_3,cb_sgmii.pl_pmod[1]})) |-> cb_sgmii.pl_pmod[1] == cb_sgmii.cnt_3[23]);

  // Mapping change coupling (no spurious toggles)
  ap_led0_change_coupled:  assert property (@cb_ps $changed(cb_ps.pl_led[0])  |-> $changed(cb_ps.cnt_0[23]));
  ap_led1_change_coupled:  assert property (@cb_ps $changed(cb_ps.pl_led[1])  |-> $changed(cb_ps.cnt_1[24]));
  ap_pmod0_change_coupled: assert property (@cb_ps $changed(cb_ps.pl_pmod[0]) |-> $changed(cb_ps.cnt_2[24]));
  ap_pmod1_change_coupled: assert property (@cb_sgmii $changed(cb_sgmii.pl_pmod[1]) |-> $changed(cb_sgmii.cnt_3[23]));

  // Optional sanity: differential refclk should be complementary
  ap_refclk_complementary: assert property (@(posedge PL_SGMII_REFCLK_125M_P)
    !$isunknown(PL_SGMII_REFCLK_125M_N) |-> (PL_SGMII_REFCLK_125M_N == ~PL_SGMII_REFCLK_125M_P)
  );

  // Coverage: wraps and visible output activity
  cv_cnt0_wrap:  cover property (@cb_ps !$isunknown($past(cb_ps.cnt_0)) && $past(cb_ps.cnt_0)==CNT0_WRAP && cb_ps.cnt_0==0);
  cv_cnt1_wrap:  cover property (@cb_ps !$isunknown($past(cb_ps.cnt_1)) && $past(cb_ps.cnt_1)==CNT1_WRAP && cb_ps.cnt_1==0);
  cv_cnt2_wrap:  cover property (@cb_ps !$isunknown($past(cb_ps.cnt_2)) && $past(cb_ps.cnt_2)==CNT2_WRAP && cb_ps.cnt_2==0);
  cv_cnt3_wrap:  cover property (@cb_sgmii !$isunknown($past(cb_sgmii.cnt_3)) && $past(cb_sgmii.cnt_3)==CNT3_WRAP && cb_sgmii.cnt_3==0);

  cv_led0_tog:   cover property (@cb_ps $changed(cb_ps.pl_led[0]));
  cv_led1_tog:   cover property (@cb_ps $changed(cb_ps.pl_led[1]));
  cv_pmod0_tog:  cover property (@cb_ps $changed(cb_ps.pl_pmod[0]));
  cv_pmod1_tog:  cover property (@cb_sgmii $changed(cb_sgmii.pl_pmod[1]));

endmodule