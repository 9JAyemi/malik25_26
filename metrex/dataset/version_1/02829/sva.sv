// SVA for wb_async_reg
// Bind these assertions to the DUT type
bind wb_async_reg wb_async_reg_sva();

module wb_async_reg_sva;

  // ------------------------
  // Reset behavior
  // ------------------------
  // Master domain reset clears important regs/outs next cycle
  assert property (@(posedge wbm_clk) wbm_rst |=> (wbm_adr_i_reg==0 && wbm_dat_i_reg==0 && wbm_dat_o==0 &&
                                                  wbm_we_i_reg==0 && wbm_sel_i_reg==0 && wbm_stb_i_reg==0 &&
                                                  wbm_ack_o==0 && wbm_err_o==0 && wbm_rty_o==0 && wbm_cyc_i_reg==0));
  // Slave domain reset clears important regs/outs next cycle
  assert property (@(posedge wbs_clk) wbs_rst |=> (wbs_adr_o==0 && wbs_dat_i_reg==0 && wbs_dat_o==0 &&
                                                  wbs_we_o==0 && wbs_sel_o==0 && wbs_stb_o==0 &&
                                                  wbs_ack_i_reg==0 && wbs_err_i_reg==0 && wbs_rty_i_reg==0 &&
                                                  wbs_cyc_o==0 && wbs_done_reg==0));

  // ------------------------
  // 3-FF synchronizers behave as pipelines (no glitches)
  // ------------------------
  assert property (@(posedge wbm_clk) disable iff (wbm_rst) wbm_done_sync2 == $past(wbm_done_sync1));
  assert property (@(posedge wbm_clk) disable iff (wbm_rst) wbm_done_sync3 == $past(wbm_done_sync2));

  assert property (@(posedge wbs_clk) disable iff (wbs_rst) wbs_cyc_o_sync2 == $past(wbs_cyc_o_sync1));
  assert property (@(posedge wbs_clk) disable iff (wbs_rst) wbs_cyc_o_sync3 == $past(wbs_cyc_o_sync2));
  assert property (@(posedge wbs_clk) disable iff (wbs_rst) wbs_stb_o_sync2 == $past(wbs_stb_o_sync1));
  assert property (@(posedge wbs_clk) disable iff (wbs_rst) wbs_stb_o_sync3 == $past(wbs_stb_o_sync2));

  // ------------------------
  // Master-domain response protocol
  // ------------------------
  // Response flags are 0-or-1 hot
  assert property (@(posedge wbm_clk) disable iff (wbm_rst) $onehot0({wbm_ack_o, wbm_err_o, wbm_rty_o}));

  // Define the synchronized done pulse
  wire wbm_done_pulse = (wbm_done_sync2 & ~wbm_done_sync3);

  // A done pulse produces exactly one response flag next cycle
  assert property (@(posedge wbm_clk) disable iff (wbm_rst) wbm_done_pulse |=> $onehot({wbm_ack_o, wbm_err_o, wbm_rty_o}));

  // No response without a prior done pulse
  assert property (@(posedge wbm_clk) disable iff (wbm_rst) (wbm_ack_o || wbm_err_o || wbm_rty_o) |-> $past(wbm_done_pulse));

  // Response flags are single-cycle pulses
  assert property (@(posedge wbm_clk) disable iff (wbm_rst) (wbm_ack_o || wbm_err_o || wbm_rty_o) |=> !(wbm_ack_o || wbm_err_o || wbm_rty_o));

  // On done, internal STB/WE drop next cycle
  assert property (@(posedge wbm_clk) disable iff (wbm_rst) wbm_done_pulse |=> (!wbm_stb_i_reg && !wbm_we_i_reg));

  // While request active and not done, request registers remain stable
  assert property (@(posedge wbm_clk) disable iff (wbm_rst)
                    (wbm_cyc_i_reg && wbm_stb_i_reg && !wbm_done_pulse) |=> 
                    (wbm_adr_i_reg==$past(wbm_adr_i_reg) && wbm_dat_i_reg==$past(wbm_dat_i_reg) &&
                     wbm_we_i_reg==$past(wbm_we_i_reg)   && wbm_sel_i_reg==$past(wbm_sel_i_reg) &&
                     wbm_stb_i_reg==$past(wbm_stb_i_reg) && wbm_cyc_i_reg==$past(wbm_cyc_i_reg)));

  // Any response only occurs when cycle is active
  assert property (@(posedge wbm_clk) disable iff (wbm_rst)
                    (wbm_ack_o || wbm_err_o || wbm_rty_o) |-> wbm_cyc_i_reg);

  // ------------------------
  // Slave-domain request/response protocol
  // ------------------------
  // Define start pulse from synchronized STB
  wire wbs_start_pulse = (wbs_stb_o_sync2 & ~wbs_stb_o_sync3);

  // On start pulse, next cycle slave-side outputs capture master-latched values
  assert property (@(posedge wbs_clk) disable iff (wbs_rst)
                    wbs_start_pulse |=> (wbs_adr_o == $past(wbm_adr_i_reg) &&
                                         wbs_dat_o == $past(wbm_dat_i_reg) &&
                                         wbs_we_o  == $past(wbm_we_i_reg)   &&
                                         wbs_sel_o == $past(wbm_sel_i_reg)  &&
                                         wbs_stb_o == $past(wbm_stb_i_reg)  &&
                                         wbs_cyc_o == $past(wbm_cyc_i_reg)));

  // When slave asserts ack/err/rty, next cycle deassert STB and latch done
  assert property (@(posedge wbs_clk) disable iff (wbs_rst)
                    (wbs_ack_i || wbs_err_i || wbs_rty_i) |=> (!wbs_stb_o && wbs_done_reg));

  // While waiting for response, hold request fields stable
  assert property (@(posedge wbs_clk) disable iff (wbs_rst)
                    (wbs_stb_o && !(wbs_ack_i || wbs_err_i || wbs_rty_i)) |=> 
                    (wbs_adr_o==$past(wbs_adr_o) && wbs_dat_o==$past(wbs_dat_o) &&
                     wbs_we_o==$past(wbs_we_o)   && wbs_sel_o==$past(wbs_sel_o) &&
                     wbs_cyc_o==$past(wbs_cyc_o)));

  // On synchronized CYC fall, clear all slave-side outputs next cycle
  assert property (@(posedge wbs_clk) disable iff (wbs_rst)
                    (~wbs_cyc_o_sync2 & wbs_cyc_o_sync3) |=> 
                    (wbs_cyc_o==0 && wbs_stb_o==0 && wbs_we_o==0 &&
                     wbs_dat_o==0 && wbs_sel_o==0 && wbs_adr_o==0));

  // wbs_done_reg holds unless a new start or cyc-clearing event occurs
  assert property (@(posedge wbs_clk) disable iff (wbs_rst)
                    (wbs_done_reg && !(wbs_start_pulse || (~wbs_cyc_o_sync2 & wbs_cyc_o_sync3))) |=> wbs_done_reg);

  // ------------------------
  // Coverage
  // ------------------------
  // Write transaction completing with ACK
  cover property (@(posedge wbm_clk) disable iff (wbm_rst)
                   (wbm_cyc_i_reg && wbm_stb_i_reg && wbm_we_i_reg) ##[1:$] wbm_done_pulse ##1 wbm_ack_o);

  // Read transaction completing with ACK
  cover property (@(posedge wbm_clk) disable iff (wbm_rst)
                   (wbm_cyc_i_reg && wbm_stb_i_reg && !wbm_we_i_reg) ##[1:$] wbm_done_pulse ##1 wbm_ack_o);

  // Error completion
  cover property (@(posedge wbm_clk) disable iff (wbm_rst)
                   (wbm_cyc_i_reg && wbm_stb_i_reg) ##[1:$] wbm_done_pulse ##1 wbm_err_o);

  // Retry completion
  cover property (@(posedge wbm_clk) disable iff (wbm_rst)
                   (wbm_cyc_i_reg && wbm_stb_i_reg) ##[1:$] wbm_done_pulse ##1 wbm_rty_o);

  // Back-to-back transactions
  cover property (@(posedge wbm_clk) disable iff (wbm_rst)
                   (wbm_cyc_i_reg && wbm_stb_i_reg) ##[1:$] wbm_done_pulse ##1 !wbm_stb_i_reg ##[1:10]
                   (wbm_cyc_i_reg && wbm_stb_i_reg) ##[1:$] wbm_done_pulse);

endmodule