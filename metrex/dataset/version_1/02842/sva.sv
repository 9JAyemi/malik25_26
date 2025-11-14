// SVA for module ports
// Bind into DUT (no ports needed; names resolve in bound scope)
bind ports ports_sva();
module ports_sva;

  // Default clocking for most assertions
  default clocking cb @(posedge cpu_clock); endclocking
  default disable iff (!rst_n);

  // Basic decode/handshake correctness
  assert property (busin == ~(port_enabled && !iorq_n && !rd_n));
  assert property (port_wr == (port_enabled && !iorq_n && !wr_n && iowrn_reg));
  assert property (port_rd == (port_enabled && !iorq_n && !rd_n && iordn_reg));
  // Memory read detect on negedge domain
  assert property (@(negedge cpu_clock) memreg_rd == (mem_enabled && !mreq_n && !rd_n && merdn_reg));

  // One-hotness in bit routing cases
  assert property ($onehot0({port02_rd, port03_wr, port0a_wrrd}));
  assert property ($onehot0({port05_wrrd, port0b_wrrd}));

  // dout mapping for addressed reads
  assert property (p_sctrl_rd |-> (dout[7:6]==2'b00 &&
                                   dout[5]  == mc_speed[1] &&
                                   dout[4]  == md_halfspeed &&
                                   dout[3]  == mc_speed[0] &&
                                   dout[2]  == mc_xrst &&
                                   dout[1]  == mc_ncs &&
                                   dout[0]  == sd_ncs));
  assert property (p_sstat_rd |-> (dout[7:4]==4'd0 &&
                                   dout[3]  == mc_rdy &&
                                   dout[2]  == sd_wp &&
                                   dout[1]  == sd_det &&
                                   dout[0]  == md_dreq));
  assert property ((a[5:0]==ZXCMD   && port_rd) |-> (dout == command_port_input));
  assert property ((a[5:0]==ZXDATRD && port_rd) |-> (dout == data_port_input));
  assert property ((a[5:0]==ZXSTAT  && port_rd) |-> (dout[7]==data_bit_input && dout[0]==command_bit_input));
  assert property ((a[5:0]==GSCFG0  && port_rd) |-> (dout[7]==1'b0 &&
                                                     dout[6]==mode_pan4ch &&
                                                     dout[5]==clksel1 &&
                                                     dout[4]==clksel0 &&
                                                     dout[3]==mode_expag &&
                                                     dout[2]==mode_8chans &&
                                                     dout[1]==mode_ramro &&
                                                     dout[0]==mode_norom));
  assert property (p_sdrd_rd  |-> dout == sd_dout);
  assert property (p_sdrst_rd |-> dout == sd_dout);
  assert property (p_mcrd_rd  |-> dout == mc_dout);

  // sd_din mapping (override on SD_RSTR)
  assert property (((a[5:0]==SD_RSTR) && 1'b1) |-> sd_din == 8'hFF);
  assert property (((a[5:0]!=SD_RSTR) && 1'b1) |-> sd_din == din);

  // Start strobes mapping
  assert property (sd_start == (p_sdsnd_wr | p_sdrst_rd));
  assert property (mc_start == p_mcsnd_wr);
  assert property (md_start == p_mdsnd_wr);

  // Mode page register updates
  assert property ((port00_wr && !mode_expag) |=> mode_pg0 == { $past(din[5:0]), 1'b0 });
  assert property ((port00_wr &&  mode_expag) |=> mode_pg0 == { $past(din[5:0]), $past(din[7]) });
  assert property ((port00_wr && !mode_expag) |=> mode_pg1 == { $past(din[5:0]), 1'b1 });
  assert property ((port10_wr &&  mode_expag) |=> mode_pg1 == { $past(din[5:0]), $past(din[7]) });

  // Other register updates
  assert property (port03_wr |=> data_port_output == $past(din));
  assert property (port09_wr |=> port09_bit5 == $past(din[5]));
  assert property (port0f_wr |=> {mode_pan4ch, clksel1, clksel0, mode_expag, mode_8chans, mode_ramro, mode_norom} == $past(din[6:0]));

  // Data/command bit routing behavior
  assert property (port02_rd  |-> (data_bit_wr && (data_bit_output==1'b0)));
  assert property (port03_wr  |-> (data_bit_wr && (data_bit_output==1'b1)));
  assert property (port0a_wrrd|-> (data_bit_wr && (data_bit_output==~mode_pg0[0])));
  assert property (!(port02_rd||port03_wr||port0a_wrrd) |-> !data_bit_wr);

  assert property (port05_wrrd |-> (command_bit_wr && (command_bit_output==1'b0)));
  assert property (port0b_wrrd |-> (command_bit_wr && (command_bit_output==port09_bit5)));
  assert property (!(port05_wrrd||port0b_wrrd) |-> !command_bit_wr);

  // volnum decode (only when volume ports selected)
  assert property (volports_enabled |-> (
                     ((a[5:0]==VOL1) -> (volnum==3'd0)) &&
                     ((a[5:0]==VOL2) -> (volnum==3'd1)) &&
                     ((a[5:0]==VOL3) -> (volnum==3'd2)) &&
                     ((a[5:0]==VOL4) -> (volnum==3'd3)) &&
                     ((a[5:0]==VOL5) -> (volnum==3'd4)) &&
                     ((a[5:0]==VOL6) -> (volnum==3'd5)) &&
                     ((a[5:0]==VOL7) -> (volnum==3'd6)) &&
                     ((a[5:0]==VOL8) -> (volnum==3'd7))
                   ));

  // Audio FIFO write side effects
  assert property (memreg_rd |=> (snd_wrtoggle == ~$past(snd_wrtoggle) &&
                                  snd_datnvol  == 1'b1 &&
                                  snd_data     == $past(din) &&
                                  snd_addr     == ($past(mode_8chans) ? $past(a[10:8]) : {1'b0,$past(a[9:8])})));
  assert property ((!memreg_rd && volports_enabled && port_wr) |=> (snd_wrtoggle == ~$past(snd_wrtoggle) &&
                                                                    snd_datnvol  == 1'b0 &&
                                                                    snd_data     == $past(din) &&
                                                                    snd_addr     == $past(volnum)));

  // SCTRL masked writes: effect when mask bit set
  assert property (p_sctrl_wr &&  din[0] |=> sd_ncs       == $past(din[7]));
  assert property (p_sctrl_wr &&  din[1] |=> mc_ncs       == $past(din[7]));
  assert property (p_sctrl_wr &&  din[2] |=> mc_xrst      == $past(din[7]));
  assert property (p_sctrl_wr &&  din[3] |=> mc_speed[0]  == $past(din[7]));
  assert property (p_sctrl_wr &&  din[4] |=> md_halfspeed == $past(din[7]));
  assert property (p_sctrl_wr &&  din[5] |=> mc_speed[1]  == $past(din[7]));
  // Optional: stability when mask bit clear
  assert property (p_sctrl_wr && !din[0] |=> $stable(sd_ncs));
  assert property (p_sctrl_wr && !din[1] |=> $stable(mc_ncs));
  assert property (p_sctrl_wr && !din[2] |=> $stable(mc_xrst));
  assert property (p_sctrl_wr && !din[3] |=> $stable(mc_speed[0]));
  assert property (p_sctrl_wr && !din[4] |=> $stable(md_halfspeed));
  assert property (p_sctrl_wr && !din[5] |=> $stable(mc_speed[1]));

  // LED behavior
  assert property (p_ledctr_wr |=> led == $past(din[0]));
  assert property (!p_ledctr_wr && led_toggle |=> led == ~$past(led));

  // Reset value checks (no disable iff)
  assert property (@(posedge cpu_clock) !rst_n |-> (md_halfspeed==1'b0 && mc_speed==2'b01 && mc_xrst==1'b0 && mc_ncs==1'b1 && sd_ncs==1'b1));
  assert property (@(posedge cpu_clock) !rst_n |-> ({mode_pan4ch, clksel1, clksel0, mode_expag, mode_8chans, mode_ramro, mode_norom}==7'b0110000));
  assert property (@(posedge cpu_clock) !rst_n |-> (led==1'b0));

  // Functional coverage (key features/paths)
  cover property (port00_wr);
  cover property (port10_wr);
  cover property (port03_wr);
  cover property (port02_rd);
  cover property (port05_wrrd);
  cover property (port0a_wrrd);
  cover property (port0b_wrrd);
  cover property (p_sctrl_wr);
  cover property (p_sctrl_rd);
  cover property (p_sstat_rd);
  cover property (p_sdsnd_wr);
  cover property (p_sdrd_rd);
  cover property (p_sdrst_rd);
  cover property (p_mdsnd_wr);
  cover property (p_mcsnd_wr);
  cover property (p_mcrd_rd);
  cover property (memreg_rd);
  cover property (volports_enabled && port_wr);
  cover property (memreg_rd && !mode_8chans);
  cover property (memreg_rd &&  mode_8chans);
  cover property (p_sctrl_wr && din[0]);
  cover property (p_sctrl_wr && din[1]);
  cover property (p_sctrl_wr && din[2]);
  cover property (p_sctrl_wr && din[3]);
  cover property (p_sctrl_wr && din[4]);
  cover property (p_sctrl_wr && din[5]);
  cover property (p_ledctr_wr);
  cover property (led_toggle);
  cover property (a[5:0]==ZXSTAT && port_rd);

endmodule