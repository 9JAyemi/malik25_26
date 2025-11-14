// SVA for etx_cfg
module etx_cfg_sva;
  // Address map (mi_addr[6:2])
  localparam [4:0] A_VER  = 5'b00000;
  localparam [4:0] A_CFG  = 5'b00010;
  localparam [4:0] A_STA  = 5'b00011;
  localparam [4:0] A_GPIO = 5'b00100;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic decode
  assert property (ecfg_write == (mi_en && mi_we));
  assert property (ecfg_read  == (mi_en && !mi_we));
  assert property (!(ecfg_write && ecfg_read));
  assert property ($onehot0({ecfg_version_write, ecfg_tx_config_write, ecfg_tx_status_write, ecfg_tx_gpio_write}));
  assert property (ecfg_version_write    == (ecfg_write && (mi_addr[6:2] == A_VER)));
  assert property (ecfg_tx_config_write  == (ecfg_write && (mi_addr[6:2] == A_CFG)));
  assert property (ecfg_tx_status_write  == (ecfg_write && (mi_addr[6:2] == A_STA)));
  assert property (ecfg_tx_gpio_write    == (ecfg_write && (mi_addr[6:2] == A_GPIO)));

  // Reset values
  assert property (reset |-> ecfg_version_reg     == DEFAULT_VERSION);
  assert property (reset |-> ecfg_tx_config_reg   == 11'b0);
  assert property (reset |-> ecfg_tx_status_reg   == 3'b0);

  // Register updates and hold
  assert property (ecfg_version_write   |=> ecfg_version_reg   == $past(mi_din[15:0]));
  assert property (!ecfg_version_write  |=> $stable(ecfg_version_reg));

  assert property (ecfg_tx_config_write |=> ecfg_tx_config_reg == $past(mi_din[10:0]));
  assert property (!ecfg_tx_config_write|=> $stable(ecfg_tx_config_reg));

  assert property (ecfg_tx_status_write |=> ecfg_tx_status_reg == $past(tx_status[2:0]));
  assert property (!ecfg_tx_status_write|=> $stable(ecfg_tx_status_reg));

  assert property (ecfg_tx_gpio_write   |=> ecfg_tx_gpio_reg   == $past(mi_din[8:0]));
  assert property (!ecfg_tx_gpio_write  |=> $stable(ecfg_tx_gpio_reg));

  // Readback mux behavior
  assert property (ecfg_read && (mi_addr[6:2]==A_VER)
                   |=> mi_dout == {16'b0, $past(ecfg_version_reg)});
  assert property (ecfg_read && (mi_addr[6:2]==A_CFG)
                   |=> mi_dout == {21'b0, $past(ecfg_tx_config_reg)});
  assert property (ecfg_read && (mi_addr[6:2]==A_STA)
                   |=> mi_dout == {16'b0, $past(tx_status[15:3]), $past(ecfg_tx_status_reg)});
  assert property (ecfg_read && (mi_addr[6:2]==A_GPIO)
                   |=> mi_dout == {23'b0, $past(ecfg_tx_gpio_reg)});
  assert property (ecfg_read && !(mi_addr[6:2] inside {A_VER,A_CFG,A_STA,A_GPIO})
                   |=> mi_dout == 32'd0);
  assert property (!ecfg_read |=> mi_dout == 32'd0);

  // Output mapping and knownness
  assert property (tx_enable === 1'b1);
  assert property (mmu_enable        == ecfg_tx_config_reg[1]);
  assert property (remap_enable      == (ecfg_tx_config_reg[3:2] == 2'b01));
  assert property (ctrlmode          == ecfg_tx_config_reg[7:4]);
  assert property (ctrlmode_bypass   == ecfg_tx_config_reg[8]);
  assert property (gpio_enable       == (ecfg_tx_config_reg[10:9] == 2'b01));
  assert property (gpio_data         == ecfg_tx_gpio_reg);
  assert property (!$isunknown({mmu_enable, remap_enable, ctrlmode, ctrlmode_bypass, gpio_enable}));

  // Functional coverage
  cover property (ecfg_version_write);
  cover property (ecfg_tx_config_write);
  cover property (ecfg_tx_status_write);
  cover property (ecfg_tx_gpio_write);

  cover property (ecfg_read && (mi_addr[6:2]==A_VER));
  cover property (ecfg_read && (mi_addr[6:2]==A_CFG));
  cover property (ecfg_read && (mi_addr[6:2]==A_STA));
  cover property (ecfg_read && (mi_addr[6:2]==A_GPIO));

  cover property ($rose(mmu_enable));
  cover property ($fell(mmu_enable));
  cover property ($rose(remap_enable));
  cover property ($rose(gpio_enable));
  cover property ($changed(ctrlmode) && ctrlmode != 4'b0000);
  cover property ($rose(ctrlmode_bypass));
endmodule

bind etx_cfg etx_cfg_sva etx_cfg_sva_i();