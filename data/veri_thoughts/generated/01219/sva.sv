module digitalclock_sva (
  input logic clk,
  input logic reset,
  input logic [3:0] hour,
  input logic [5:0] minute,
  input logic ampm,
  input logic valid,
  // Internal DUT signals used by assertions (must be connected via bind)
  input logic [3:0] hour_count,
  input logic [5:0] minute_count
);

  ///// Output mirroring of internal counters /////
  // hour output must mirror hour_count.
  outputs_match_hour: assert property (
    @(posedge clk) disable iff (reset) hour == hour_count
  );
  // minute output must mirror minute_count.
  outputs_match_minute: assert property (
    @(posedge clk) disable iff (reset) minute == minute_count
  );

  ///// Synchronous reset effects (next cycle) /////
  // On reset, next-cycle hour_count=1 and minute_count=0.
  reset_sets_counts: assert property (
    @(posedge clk) reset |-> ##1 (hour_count == 4'd1 && minute_count == 6'd0)
  );
  // On reset, next-cycle ampm=0.
  reset_clears_ampm: assert property (
    @(posedge clk) reset |-> ##1 (ampm == 1'b0)
  );

  ///// Minute counter behavior /////
  // If minute_count != 59, it increments by 1 next cycle.
  minute_increments: assert property (
    @(posedge clk) disable iff (reset)
      (minute_count != 6'd59) |-> ##1 (minute_count == $past(minute_count) + 6'd1)
  );
  // If minute_count == 59, it wraps to 0 next cycle.
  minute_wraps_at_59: assert property (
    @(posedge clk) disable iff (reset)
      (minute_count == 6'd59) |-> ##1 (minute_count == 6'd0)
  );

  ///// Hour counter behavior /////
  // If minute_count != 59, hour_count holds its value next cycle.
  hour_holds_when_minute_not_59: assert property (
    @(posedge clk) disable iff (reset)
      (minute_count != 6'd59) |-> ##1 (hour_count == $past(hour_count))
  );
  // If minute_count == 59 and hour_count != 12, hour_count increments next cycle.
  hour_increments_on_minute_wrap: assert property (
    @(posedge clk) disable iff (reset)
      (minute_count == 6'd59 && hour_count != 4'd12) |-> ##1 (hour_count == $past(hour_count) + 4'd1)
  );
  // If minute_count == 59 and hour_count == 12, hour_count wraps to 1 next cycle.
  hour_wraps_from_12_on_minute_wrap: assert property (
    @(posedge clk) disable iff (reset)
      (minute_count == 6'd59 && hour_count == 4'd12) |-> ##1 (hour_count == 4'd1)
  );

  ///// AM/PM behavior /////
  // When hour_count == 12, ampm toggles next cycle.
  ampm_toggles_at_hour_12: assert property (
    @(posedge clk) disable iff (reset)
      (hour_count == 4'd12) |-> ##1 (ampm == ~$past(ampm))
  );
  // When hour_count != 12, ampm holds its value next cycle.
  ampm_holds_when_not_12: assert property (
    @(posedge clk) disable iff (reset)
      (hour_count != 4'd12) |-> ##1 (ampm == $past(ampm))
  );

  ///// valid flag behavior /////
  // If time is 12:00 this cycle, valid is 1 next cycle.
  valid_high_next_if_12_00: assert property (
    @(posedge clk) disable iff (reset)
      (hour_count == 4'd12 && minute_count == 6'd0) |-> ##1 (valid == 1'b1)
  );
  // If time is not 12:00 this cycle, valid is 0 next cycle.
  valid_low_next_if_not_12_00: assert property (
    @(posedge clk) disable iff (reset)
      !(hour_count == 4'd12 && minute_count == 6'd0) |-> ##1 (valid == 1'b0)
  );

endmodule