// SVA for touch_sensor
// Bind into the DUT so we can directly see internals.
module touch_sensor_sva;

  // 1) touch_out must mirror touch_detected (combinationally, no extra storage)
  ap_out_mirrors_reg: assert property (
    @(posedge touch_detected or negedge touch_detected or posedge touch_out or negedge touch_out)
      touch_out === touch_detected
  );

  // Optional stricter 0-delta mirror check on any change of touch_detected
  ap_out_mirror_0delta: assert property (
    @(posedge touch_detected or negedge touch_detected)
      ##0 (touch_out === touch_detected)
  );

  // 2) touch_detected never falls (sticky-1 behavior)
  ap_reg_never_falls: assert property (@(negedge touch_detected) 0);

  // 3) touch_out never falls (sticky-1 behavior reflected at output)
  ap_out_never_falls: assert property (@(negedge touch_out) 0);

  // 4) On posedge of touch_in, touch_detected is not updated immediately (due to #1 delay)
  ap_no_immediate_update: assert property (@(posedge touch_in) $stable(touch_detected));

  // 5) Once a touch_in rising edge has occurred, touch_out must be high by the next touch_in rising edge
  ap_out_high_by_next_rise: assert property (@(posedge touch_in) 1 |=> touch_out);

  // 6) Any rise of touch_detected or touch_out must occur only after at least one touch_in rise
  bit seen_rise;
  initial seen_rise = 0;
  always @(posedge touch_in) seen_rise <= 1;

  ap_reg_rise_after_input_rise: assert property (@(posedge touch_detected) seen_rise);
  ap_out_rise_after_input_rise: assert property (@(posedge touch_out)      seen_rise);

  // Coverage
  cp_touch_seen:               cover property (@(posedge touch_in) 1);
  cp_out_rises:                cover property (@(posedge touch_out) 1);
  cp_out_high_by_next_rise:    cover property (@(posedge touch_in) !touch_out |=> touch_out);

endmodule

bind touch_sensor touch_sensor_sva sva();