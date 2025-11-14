// SVA for my_module — concise, high-quality checks and coverage
module my_module_sva #(parameter bit CHECK_DIFFCLK_INV = 0) ();

  default clocking cb @(posedge sgmii_refclk_p); endclocking
  default disable iff ($initstate);

  // Counters must increment by 1 each clock once past value is known
  assert property (!$isunknown($past(cnt_0)) |-> cnt_0 == $past(cnt_0) + 1);
  assert property (!$isunknown($past(cnt_1)) |-> cnt_1 == $past(cnt_1) + 1);
  assert property (!$isunknown($past(cnt_2)) |-> cnt_2 == $past(cnt_2) + 1);
  assert property (!$isunknown($past(cnt_3)) |-> cnt_3 == $past(cnt_3) + 1);

  // LED/PMOD mappings to counter MSBs and button
  assert property (!$isunknown(cnt_0[23]) |-> pl_led[0]  == cnt_0[23]);
  assert property (!$isunknown(cnt_1[23]) |-> pl_led[1]  == cnt_1[23]);
  assert property (!$isunknown(cnt_3[23]) |-> pl_pmod[0] == cnt_3[23]);
  assert property (!$isunknown(pl_btn)    |-> pl_pmod[1] == pl_btn);

  // Button passthrough to MDIO clock
  assert property (!$isunknown(pl_btn) |-> mdio_mdc == pl_btn);

  // TX is bitwise inversion of RX (combinational mapping, checked each clk)
  assert property (!$isunknown(sgmii_rxn) |-> sgmii_txn == ~sgmii_rxn);
  assert property (!$isunknown(sgmii_rxp) |-> sgmii_txp == ~sgmii_rxp);

  // Optional: differential refclk should be complementary (checked on both edges)
  generate if (CHECK_DIFFCLK_INV) begin
    assert property (@(posedge sgmii_refclk_p or negedge sgmii_refclk_p)
                     sgmii_refclk_n == ~sgmii_refclk_p);
  end endgenerate

  // Coverage: observe activity on MSBs, button, and RX->TX mapping
  cover property ($changed(cnt_0[23]));
  cover property ($changed(cnt_1[23]));
  cover property ($changed(cnt_2[23]));
  cover property ($changed(cnt_3[23]));

  cover property ($changed(pl_btn) ##0 (mdio_mdc == pl_btn && pl_pmod[1] == pl_btn));

  cover property ($changed(sgmii_rxn) ##0 (sgmii_txn == ~sgmii_rxn));
  cover property ($changed(sgmii_rxp) ##0 (sgmii_txp == ~sgmii_rxp));

endmodule

bind my_module my_module_sva #(.CHECK_DIFFCLK_INV(0)) u_my_module_sva();