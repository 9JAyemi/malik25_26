module up_down_counter_sva (
  input logic clk,
  input logic reset,
  input logic enable,
  input logic control,
  input logic [2:0] count
);

  ///// Reset behavior /////
  // While reset is HIGH at a clock edge, count is 0.
  check_reset_forces_zero: assert property (
    @(posedge clk) reset |-> (count == 3'd0)
  );

  ///// Hold/update rules /////
  // When disabled, count holds its previous value.
  check_hold_when_disabled: assert property (
    @(posedge clk) disable iff (reset) (!enable) |=> (count == $past(count))
  );

  // When enabled and control=1, count increments by 1 (mod 8).
  check_increment_when_enabled: assert property (
    @(posedge clk) disable iff (reset) (enable && control) |=> (count == ($past(count) + 3'd1))
  );

  // When enabled and control=0, count decrements by 1 (mod 8).
  check_decrement_when_enabled: assert property (
    @(posedge clk) disable iff (reset) (enable && !control) |=> (count == ($past(count) - 3'd1))
  );

  // When enabled, count must change value next cycle.
  check_change_on_enable: assert property (
    @(posedge clk) disable iff (reset) (enable) |=> (count != $past(count))
  );

  ///// Wrap-around corner cases /////
  // Increment wrap-around: 7 -> 0 when enabled and control=1.
  check_increment_wrap: assert property (
    @(posedge clk) disable iff (reset) (enable && control && ($past(count) == 3'd7)) |=> (count == 3'd0)
  );

  // Decrement wrap-around: 0 -> 7 when enabled and control=0.
  check_decrement_wrap: assert property (
    @(posedge clk) disable iff (reset) (enable && !control && ($past(count) == 3'd0)) |=> (count == 3'd7)
  );

  ///// Sanity /////
  // Count is always within 3-bit range.
  check_count_range: assert property (
    @(posedge clk) (count <= 3'd7)
  );

endmodule