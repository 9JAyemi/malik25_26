// SVA for debnce: concise, high-quality checks and coverage
// Bind this module to the DUT
module debnce_sva;
  default clocking cb @(posedge clk); endclocking

  bit f_past_valid;
  always @(posedge clk) f_past_valid <= 1'b1;

  // Basic consistency / no-X
  a_sat_def:   assert property (sat == (ctr == 16'hffff));
  a_no_x:      assert property (!$isunknown({sync, ctr, dly, sat, event_on, event_off}));

  // Counter next-state behavior
  a_ctr_rst_on_sync0: assert property (sync==1'b0 |=> ctr==16'h0000);
  a_ctr_inc:          assert property ((sync && !sat) |=> ctr == $past(ctr) + 16'd1);
  a_ctr_hold_at_sat:  assert property ((sync &&  sat) |=> ctr == $past(ctr));

  // Pipeline register
  a_dly_is_prev_sat:  assert property (disable iff(!f_past_valid) dly == $past(sat));

  // Event generation (edge detection of sat)
  a_on_from_rose:     assert property ($rose(sat) |=> event_on);
  a_off_from_fall:    assert property ($fell(sat) |=> event_off);
  a_on_func_prev:     assert property (disable iff(!f_past_valid) event_on  |-> $past((!dly) && sat));
  a_off_func_prev:    assert property (disable iff(!f_past_valid) event_off |-> $past((!sat) && dly));
  a_on_single_pulse:  assert property (event_on  |=> !event_on);
  a_off_single_pulse: assert property (event_off |=> !event_off);
  a_events_exclusive: assert property (!(event_on && event_off));
  a_no_spurious_when_sat_static:
                      assert property (disable iff(!f_past_valid) (sat==$past(sat)) |=> (!event_on && !event_off));

  // Coverage
  c_sat_rise:     cover property ($rose(sat));
  c_sat_fall:     cover property ($fell(sat));
  c_event_on:     cover property (event_on);
  c_event_off:    cover property (event_off);
  c_hold_at_sat:  cover property (sat && sync ##1 sat && sync);
endmodule

bind debnce debnce_sva sva();