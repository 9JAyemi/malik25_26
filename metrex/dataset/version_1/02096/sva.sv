// SVA for rgmii. Bind into the DUT instance.
module rgmii_sva;

  // Use TX clock for default sampling; gate checks during reset to avoid X-propagation noise.
  default clocking cb_tx @(posedge generated_clk); endclocking
  default disable iff (reset);

  // TX datapath and control mapping
  a_tx_map: assert property (
      (phy_txd_rising      == mac_txd[3:0])  &&
      (phy_txd_falling     == mac_txd[7:4])  &&
      (phy_tx_ctl_rising   == mac_tx_en)     &&
      (phy_tx_ctl_falling  == (mac_tx_en ^ mac_tx_er))
  );

  // TX clocks pass-through on both edges
  a_tx_clk_eq_pos: assert property (@(posedge generated_clk) phy_gtx_clk == generated_clk && mac_tx_clk == generated_clk);
  a_tx_clk_eq_neg: assert property (@(negedge generated_clk) phy_gtx_clk == generated_clk && mac_tx_clk == generated_clk);

  // Collision logic (original and simplified forms)
  a_col_logic_expr: assert property (mac_col == ((mac_crs & mac_tx_en) | (mac_rx_dv & mac_tx_en)));
  a_col_simplify:   assert property (mac_col == (mac_tx_en & mac_crs));

  // RX datapath and control mapping (sampled on RX clock)
  a_rx_map: assert property (@(posedge phy_rx_clk)
      (mac_rxd[3:0]  == phy_rxd_rising)                &&
      (mac_rxd[7:4]  == phy_rxd_falling)               &&
      (mac_rx_dv     == phy_rx_ctl_rising)             &&
      (mac_rx_er     == (phy_rx_ctl_falling ^ phy_rx_ctl_rising))
  );

  // RX clock pass-through on both edges
  a_rx_clk_eq_pos: assert property (@(posedge phy_rx_clk) mac_rx_clk == phy_rx_clk);
  a_rx_clk_eq_neg: assert property (@(negedge phy_rx_clk) mac_rx_clk == phy_rx_clk);

  // CRS logic exactly matches specified expression
  a_crs_logic: assert property (
      mac_crs ==
      ( mac_rx_dv
        | (mac_rx_er && mac_rxd == 8'hFF)
        | (mac_rx_er && mac_rxd == 8'h0E)
        | (mac_rx_er && mac_rxd == 8'h0F)
        | (mac_rx_er && mac_rxd == 8'h1F)
      )
  );

  // Functional coverage

  // TX control XOR cases
  c_tx_ctl_xor_10: cover property (@(posedge generated_clk)  mac_tx_en && !mac_tx_er && phy_tx_ctl_falling);
  c_tx_ctl_xor_01: cover property (@(posedge generated_clk) !mac_tx_en &&  mac_tx_er && phy_tx_ctl_falling);

  // RX control XOR cases and no-error case
  c_rx_er_10: cover property (@(posedge phy_rx_clk)  phy_rx_ctl_rising && !phy_rx_ctl_falling && mac_rx_er);
  c_rx_er_01: cover property (@(posedge phy_rx_clk) !phy_rx_ctl_rising &&  phy_rx_ctl_falling && mac_rx_er);
  c_rx_er_00: cover property (@(posedge phy_rx_clk) !phy_rx_ctl_rising && !phy_rx_ctl_falling && !mac_rx_er);

  // CRS via DV and via specific error/data combinations
  c_crs_by_dv: cover property (@(posedge phy_rx_clk) mac_rx_dv && mac_crs);
  c_crs_by_ff: cover property (@(posedge phy_rx_clk) mac_rx_er && mac_rxd==8'hFF && mac_crs);
  c_crs_by_0E: cover property (@(posedge phy_rx_clk) mac_rx_er && mac_rxd==8'h0E && mac_crs);
  c_crs_by_0F: cover property (@(posedge phy_rx_clk) mac_rx_er && mac_rxd==8'h0F && mac_crs);
  c_crs_by_1F: cover property (@(posedge phy_rx_clk) mac_rx_er && mac_rxd==8'h1F && mac_crs);

  // Collision asserted while transmitting and carrier present
  c_mac_col: cover property (@(posedge generated_clk) mac_tx_en && mac_crs && mac_col);

endmodule

bind rgmii rgmii_sva rgmii_sva_i();