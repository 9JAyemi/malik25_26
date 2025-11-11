// SVA for cog_vid: concise, high-value checks and coverage
// Bind into DUT: bind cog_vid cog_vid_sva sva();

module cog_vid_sva;

  // Basic derives/gating
  // vclk is combinationally gated; assert basic implications
  assert property (@(posedge clk_vid) vclk |-> enable);
  assert property (@(posedge clk_vid) !enable |-> !vclk);
  assert property (enable == (|vid[30:29]));

  // clk_cog domain: vid and scl behavior
  assert property (@(posedge clk_cog) !ena |-> vid == 32'b0);
  assert property (@(posedge clk_cog) disable iff (!ena) setvid |=> vid == $past(data));
  assert property (@(posedge clk_cog) disable iff (!ena) !setvid |=> vid == $past(vid));

  assert property (@(posedge clk_cog) setscl |=> scl == $past(data));
  assert property (@(posedge clk_cog) !setscl |=> scl == $past(scl));

  // vclk domain: counters and timers
  assert property (@(posedge vclk) new_set |=> cnts == $past(scl[19:12]));
  assert property (@(posedge vclk) new_set |=> cnt  == $past(scl[19:12]));
  assert property (@(posedge vclk) !new_set && new_cnt |=> cnt == $past(cnts));
  assert property (@(posedge vclk) !new_set && !new_cnt |=> cnt == $past(cnt) - 1);

  assert property (@(posedge vclk) new_set |=> set == $past(scl[11:0]));
  assert property (@(posedge vclk) !new_set |=> set == $past(set) - 1);

  // Pixels/colors pipeline
  assert property (@(posedge vclk) new_set |=> pixels == $past(pixel));
  assert property (@(posedge vclk) !new_set && new_cnt &&  vid[28] |=> pixels == {$past(pixels)[31:30], $past(pixels)[31:2]});
  assert property (@(posedge vclk) !new_set && new_cnt && !vid[28] |=> pixels == {$past(pixels)[31],     $past(pixels)[31:1]});
  assert property (@(posedge vclk) !new_set && !new_cnt |=> pixels == $past(pixels));

  assert property (@(posedge vclk) new_set |=> colors == $past(color));
  assert property (@(posedge vclk) !new_set |=> colors == $past(colors));

  // cap/snc handshake and ACK
  assert property (@(posedge vclk) snc[1] |-> cap == 1'b0);
  assert property (@(posedge vclk) !snc[1] && new_set |=> cap == 1'b1);

  assert property (@(posedge clk_cog) enable |=> snc[1] == $past(snc[0]) && snc[0] == $past(cap));
  assert property (@(posedge clk_cog) !enable |=> snc == $past(snc));
  assert property (@(posedge clk_cog) ack == snc[0]);

  // Color/path calculations
  assert property (@(posedge vclk) discrete == colorx[7:0]);
  assert property (@(posedge vclk) phase == $past(phase) + 1);
  assert property (@(posedge vclk) baseband == {discrete[3] && colorphs[3], vid[26] ? colormod : discrete[2:0]});
  assert property (@(posedge vclk) composite == (vid[27] ? colormod : discrete[2:0]));
  assert property (@(posedge vclk) broadcast[3] == (carrier ^ aural[vid[25:23]]) &&
                                 broadcast[2:0] == level[{carrier, composite}*4 +: 3]);

  // outp and pin_out formation
  assert property (@(posedge vclk)  vid[30] &&  vid[29] |-> outp == {baseband, broadcast});
  assert property (@(posedge vclk)  vid[30] && !vid[29] |-> outp == {broadcast, baseband});
  assert property (@(posedge vclk) !vid[30]              |-> outp == discrete);

  assert property ( enable |-> pin_out == ({24'b0, (outp & vid[7:0])} << {vid[10:9], 3'b000}));
  assert property (!enable |-> pin_out == 32'b0);

  // X-safety on key outputs when enabled/active
  assert property (enable |-> !$isunknown(pin_out));
  assert property (@(posedge clk_cog) !$isunknown(ack));

  // Coverage: key modes and handshakes
  cover property (@(posedge clk_vid) $rose(enable));
  cover property (@(posedge vclk) new_set);
  cover property (@(posedge vclk) new_cnt &&  vid[28]);
  cover property (@(posedge vclk) new_cnt && !vid[28]);
  cover property (@(posedge vclk)  vid[30] &&  vid[29]); // outp = {baseband,broadcast}
  cover property (@(posedge vclk)  vid[30] && !vid[29]); // outp = {broadcast,baseband}
  cover property (@(posedge vclk) !vid[30]);             // outp = discrete
  cover property (@(posedge vclk) vid[27]);              // composite from colormod
  cover property (@(posedge vclk) vid[26]);              // baseband uses colormod
  cover property (@(posedge vclk) ##1 (vid[10:9]==2'b00) ##1 (vid[10:9]==2'b01) ##1 (vid[10:9]==2'b10) ##1 (vid[10:9]==2'b11));
  cover property (@(posedge clk_cog) enable ##1 ack ##1 snc[1]); // handshake observed

endmodule

bind cog_vid cog_vid_sva sva();