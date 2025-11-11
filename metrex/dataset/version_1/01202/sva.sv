// SystemVerilog Assertions for led_flasher
// Bind into the DUT: bind led_flasher led_flasher_sva sva();

module led_flasher_sva;

  // Default clock
  default clocking cb @(posedge clk); endclocking

  // Track past-valid for $past uses
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Safety: legal state encoding only
  a_state_legal: assert property (state inside {s_reset, s_off, s_on});

  // LED_out must mirror state==s_on
  a_led_out_match: assert property (LED_out == (state == s_on));

  // In s_reset, counter is always 0
  a_reset_cnt_zero: assert property (state == s_reset |-> cnt == 16'd0);

  // Reset-state transitions
  a_reset_stay:  assert property (state == s_reset && !LED_flash |=> state == s_reset);
  a_reset_to_on: assert property (state == s_reset &&  LED_flash |=> state == s_on);

  // OFF-state transitions and counter behavior
  a_off_stay:    assert property (state == s_off && LED_flash && (cnt != LOW_PERIOD) |=> state == s_off);
  a_off_to_on:   assert property (state == s_off && LED_flash && (cnt == LOW_PERIOD) |=> state == s_on && cnt == 16'd0);
  a_off_to_rst:  assert property (state == s_off && !LED_flash |=> state == s_reset);
  a_cnt_inc_off: assert property (state == s_off && LED_flash && (cnt != LOW_PERIOD) |=> cnt == $past(cnt)+1);

  // ON-state transitions and counter behavior
  a_on_stay:     assert property (state == s_on  && LED_flash && (cnt != HIGH_PERIOD) |=> state == s_on);
  a_on_to_off:   assert property (state == s_on  && LED_flash && (cnt == HIGH_PERIOD) |=> state == s_off && cnt == 16'd0);
  a_on_to_rst:   assert property (state == s_on  && !LED_flash |=> state == s_reset);
  a_cnt_inc_on:  assert property (state == s_on  && LED_flash && (cnt != HIGH_PERIOD) |=> cnt == $past(cnt)+1);

  // Reverse-direction transition guards (only-when conditions)
  a_off_to_on_cond: assert property (disable iff (!past_valid)
                                     ($past(state) == s_off && state == s_on)
                                     |-> $past(LED_flash) && ($past(cnt) == LOW_PERIOD));
  a_on_to_off_cond: assert property (disable iff (!past_valid)
                                     ($past(state) == s_on  && state == s_off)
                                     |-> $past(LED_flash) && ($past(cnt) == HIGH_PERIOD));
  a_rst_entry_cond: assert property (disable iff (!past_valid)
                                     (state == s_reset && $past(state) != s_reset)
                                     |-> !$past(LED_flash));
  a_rst_to_on_cond: assert property (disable iff (!past_valid)
                                     ($past(state) == s_reset && state == s_on)
                                     |-> $past(LED_flash));

  // No X/Z on key signals
  a_no_x: assert property (!$isunknown({state, cnt, LED_out})));

  // Coverage
  c_on_term:   cover property (state == s_on  && LED_flash && (cnt == HIGH_PERIOD));
  c_off_term:  cover property (state == s_off && LED_flash && (cnt == LOW_PERIOD));
  c_full_cycle: cover property (LED_flash && state == s_on ##[1:$] (LED_flash && state == s_off) ##[1:$] (LED_flash && state == s_on));
  c_drop_to_reset_from_on:  cover property (state == s_on  && LED_flash ##1 !LED_flash ##1 state == s_reset);
  c_drop_to_reset_from_off: cover property (state == s_off && LED_flash ##1 !LED_flash ##1 state == s_reset);
  c_led_toggle: cover property ($changed(LED_out));

endmodule

// Bind example (instantiate once globally, e.g., in TB top):
// bind led_flasher led_flasher_sva sva();