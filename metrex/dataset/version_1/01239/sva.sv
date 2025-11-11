// Bindable SVA for ps2_keyboard. Focused, high-quality checks and covers.
bind ps2_keyboard ps2_keyboard_sva sva();

module ps2_keyboard_sva;

  default clocking cb @(posedge CLK); endclocking
  default disable iff (!RESET_N);

  // Sanity
  a_outputs_match:    assert property (RX_PRESSED == rx_pressed && RX_EXTENDED == rx_extended && RX_SCAN == rx_scan);
  a_state_legal:      assert property (state inside {IDLE, START_BIT, DATA_BIT, PARITY_BIT, STOP_BIT});
  a_no_unknowns:      assert property (!$isunknown({state, bit_count, timer, rx_pressed, rx_extended, rx_scan, scan_code}));

  // Async reset values (don’t disable on reset for this check)
  a_async_reset_vals: assert property (@(posedge CLK) $fell(RESET_N) |=> (state==IDLE && bit_count==0 && timer==0 &&
                                                                         rx_pressed==0 && rx_extended==0 &&
                                                                         scan_code==0 && rx_scan==0));

  // IDLE
  a_idle_to_start:    assert property (state==IDLE && !PS2_CLK && PS2_DATA |=> state==START_BIT);
  a_idle_stay:        assert property (state==IDLE && !(!PS2_CLK && PS2_DATA) |=> state==IDLE);

  // START_BIT
  a_start_to_data:    assert property (state==START_BIT && PS2_CLK |=> state==DATA_BIT);
  a_start_hold:       assert property (state==START_BIT && !PS2_CLK |=> state==START_BIT);
  a_start_inits:      assert property (state==IDLE && !PS2_CLK && PS2_DATA |=> bit_count==0 && scan_code==0);

  // DATA_BIT capture and flow
  a_data_cap:         assert property (state==DATA_BIT && !PS2_CLK |=> scan_code[$past(bit_count)] == $past(PS2_DATA)
                                                             && bit_count == $past(bit_count)+1);
  a_data_to_par:      assert property (state==DATA_BIT && !PS2_CLK && bit_count==3'd7 |=> state==PARITY_BIT);
  a_data_hold:        assert property (state==DATA_BIT && !PS2_CLK && bit_count!=3'd7 &&
                                       !(PS2_DATA && timer==8'hFF) |=> state==DATA_BIT);

  // PARITY_BIT behavior
  function automatic bit par_ok7;
    par_ok7 = (PS2_DATA == ~(scan_code[0]^scan_code[1]^scan_code[2]^scan_code[3]^scan_code[4]^scan_code[5]^scan_code[6]));
  endfunction

  a_par_clk_high:     assert property (state==PARITY_BIT && PS2_CLK |=> state==STOP_BIT);

  a_par_ext:          assert property (state==PARITY_BIT && !PS2_CLK && par_ok7 && (scan_code==EXTENDED_CODE) &&
                                       !(PS2_DATA && timer==8'hFF) |=> rx_extended && state==IDLE);
  a_par_rel:          assert property (state==PARITY_BIT && !PS2_CLK && par_ok7 && (scan_code==RELEASE_CODE) &&
                                       !(PS2_DATA && timer==8'hFF) |=> rx_pressed==0 && state==IDLE);
  a_par_norm:         assert property (state==PARITY_BIT && !PS2_CLK && par_ok7 &&
                                       (scan_code!=EXTENDED_CODE) && (scan_code!=RELEASE_CODE) &&
                                       !(PS2_DATA && timer==8'hFF) |=> rx_scan==$past(scan_code) && rx_pressed && state==STOP_BIT);
  a_par_err:          assert property (state==PARITY_BIT && !PS2_CLK && !par_ok7 |=> state==IDLE);

  // STOP_BIT
  a_stop_to_idle:     assert property (state==STOP_BIT && PS2_CLK |=> state==IDLE);
  a_stop_hold:        assert property (state==STOP_BIT && !PS2_CLK |=> state==STOP_BIT);

  // Timer behavior
  a_timer_reset:      assert property (!PS2_CLK && !PS2_DATA |=> timer==8'h00);
  a_timer_incr:       assert property (!PS2_CLK && PS2_DATA  |=> timer==$past(timer)+1);
  a_timer_hold_clkhi: assert property (PS2_CLK |=> timer==$past(timer));
  a_timeout_idle:     assert property (!PS2_CLK && PS2_DATA && timer==8'hFF |=> state==IDLE);

  // Sticky extended flag (as implemented)
  a_ext_sticky:       assert property (rx_extended |=> rx_extended);

  // Bitcount only changes on start or data capture
  a_bitcnt_change_src: assert property ($changed(bit_count) |-> (state==DATA_BIT && !PS2_CLK) ||
                                                        (state==IDLE && !PS2_CLK && PS2_DATA));

  // Coverage
  c_full_frame:       cover property (state==IDLE ##1 state==START_BIT ##
                                      (state==DATA_BIT && !PS2_CLK)[*8] ##1 state==PARITY_BIT ##1
                                      state==STOP_BIT ##1 state==IDLE);
  c_extended_path:    cover property (state==PARITY_BIT && !PS2_CLK && par_ok7 && scan_code==EXTENDED_CODE ##1 state==IDLE);
  c_release_path:     cover property (state==PARITY_BIT && !PS2_CLK && par_ok7 && scan_code==RELEASE_CODE ##1 state==IDLE);
  c_normal_path:      cover property (state==PARITY_BIT && !PS2_CLK && par_ok7 &&
                                      (scan_code!=EXTENDED_CODE && scan_code!=RELEASE_CODE) ##1
                                      state==STOP_BIT ##1 state==IDLE);
  c_timeout:          cover property (!PS2_CLK && PS2_DATA && timer==8'hFF ##1 state==IDLE);

endmodule