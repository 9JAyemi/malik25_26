// SVA for keyboard_pressed_status
// Bind into DUT; references internal signals/arrays directly.
module keyboard_pressed_status_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Basic sanity
  a_state_legal: assert property (1 |-> state inside {RESETTING,UPDATING,SCANNING});

  // Reset behavior (override disable)
  a_rst_seq: assert property (@(posedge clk) disable iff (1'b0)
                              rst |=> state==RESETTING && addrscan==8'h00);

  // RESETTING progression and clearing
  a_reset_cnt_inc:  assert property (state==RESETTING && addrscan!=8'hFF
                                     |=> state==RESETTING && addrscan==$past(addrscan)+8'd1);
  a_reset_to_scan:  assert property (state==RESETTING && addrscan==8'hFF
                                     |=> state==SCANNING && addrscan==8'h00 && kbclean==1);
  a_reset_clears_entry: assert property ($past(state)==RESETTING && $past(addrscan)!=8'hFF
                                         |-> keybstat_ne[$past(addrscan)]==0 && keybstat_ex[$past(addrscan)]==0);
  // Ensure FF entries are 0 when exiting RESETTING (catches missing-clear bug on 8'hFF)
  a_reset_clears_ff: assert property ($past(state)==RESETTING && $past(addrscan)==8'hFF
                                      |-> keybstat_ne[8'hFF]==0 && keybstat_ex[8'hFF]==0);

  // SCANNING address increments and state transitions
  a_scan_inc:         assert property (state==SCANNING |=> addrscan==$past(addrscan)+8'd1);
  a_scan_stay:        assert property (state==SCANNING && !scan_received |=> state==SCANNING);
  a_scan_to_update:   assert property (state==SCANNING &&  scan_received |=> state==UPDATING);

  // SCANNING accumulation and end-of-scan finalize
  a_accum_step: assert property ($past(state)==SCANNING && $past(addrscan)!=8'hFF
                                 |-> keypressed_ne==($past(keypressed_ne)|keybstat_ne[$past(addrscan)]) &&
                                     keypressed_ex==($past(keypressed_ex)|keybstat_ex[$past(addrscan)]));
  a_accum_finalize: assert property ($past(state)==SCANNING && $past(addrscan)==8'hFF
                                     |-> kbclean==~($past(keypressed_ne)|$past(keypressed_ex)) &&
                                         keypressed_ne==0 && keypressed_ex==0);
  a_kbclean_changes_only_at_ff: assert property (state==SCANNING && $changed(kbclean)
                                                 |-> $past(addrscan)==8'hFF);

  // UPDATING behavior: one-cycle, kbclean low, restart scan at 0
  a_update_one_cycle:      assert property (state==UPDATING |=> state==SCANNING && addrscan==8'h00);
  a_update_drives_kb0:     assert property (state==UPDATING |-> kbclean==0);

  // Write semantics for non-extended
  a_update_ne_write: assert property ($past(state)==SCANNING && $past(scan_received) && $past(extended)==0
                                      |-> state==UPDATING && kbclean==0 && addrscan==8'h00
                                          ##1 keybstat_ne[$past(scancode,1)] == ~($past(released,1)) &&
                                              $stable(keybstat_ex[$past(scancode,1)]));
  // Write semantics for extended
  a_update_ex_write: assert property ($past(state)==SCANNING && $past(scan_received) && $past(extended)==1
                                      |-> state==UPDATING && kbclean==0 && addrscan==8'h00
                                          ##1 keybstat_ex[$past(scancode,1)] == ~($past(released,1)) &&
                                              $stable(keybstat_ne[$past(scancode,1)]));

  // Bug-catcher: FF index must affect kbclean at end-of-scan
  a_include_ff_in_clean: assert property ($past(state)==SCANNING && $past(addrscan)==8'hFF &&
                                          $past(keypressed_ne)==0 && $past(keypressed_ex)==0 &&
                                          $past(keybstat_ne[8'hFF])==1 && $past(keybstat_ex[8'hFF])==0
                                          |-> kbclean==0);

  // Coverage
  c_reset_done:        cover property (state==RESETTING && addrscan==8'hFE ##1
                                       state==RESETTING && addrscan==8'hFF ##1
                                       state==SCANNING && kbclean==1);
  c_scan_wrap:         cover property (state==SCANNING && addrscan==8'hFE ##1
                                       state==SCANNING && addrscan==8'hFF ##1
                                       state==SCANNING && addrscan==8'h00);
  c_update_ne_press:   cover property (state==SCANNING && scan_received && !extended && !released
                                       ##1 state==UPDATING ##1 state==SCANNING &&
                                       keybstat_ne[$past(scancode,1)]);
  c_update_ne_release: cover property (state==SCANNING && scan_received && !extended &&  released
                                       ##1 state==UPDATING ##1 state==SCANNING &&
                                       !keybstat_ne[$past(scancode,1)]);
  c_update_ex_press:   cover property (state==SCANNING && scan_received &&  extended && !released
                                       ##1 state==UPDATING ##1 state==SCANNING &&
                                       keybstat_ex[$past(scancode,1)]);
  c_update_ex_release: cover property (state==SCANNING && scan_received &&  extended &&  released
                                       ##1 state==UPDATING ##1 state==SCANNING &&
                                       !keybstat_ex[$past(scancode,1)]);
  c_kbclean_toggle_hi: cover property ($rose(kbclean));
  c_kbclean_toggle_lo: cover property ($fell(kbclean));
endmodule

bind keyboard_pressed_status keyboard_pressed_status_sva sva_kb_status();