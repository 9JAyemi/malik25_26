module counter_4bit_sva (
  input logic clk,
  input logic reset,
  input logic enable,
  input logic [3:0] count
);
  // On reset HIGH, next cycle count is driven to 0.
  reset_clears_next: assert property (
    @(posedge clk) reset |=> (count == 4'd0)
  );

  // If reset stays HIGH across cycles, count is 0 on the later cycle.
  reset_holds_zero: assert property (
    @(posedge clk) (reset && $past(reset)) |-> (count == 4'd0)
  );

  // On reset falling edge, count is 0 in that cycle (result of prior reset).
  count_zero_on_reset_fall: assert property (
    @(posedge clk) $fell(reset) |-> (count == 4'd0)
  );

  // With previous enable and no reset, count increments by 1 (mod 16).
  increment_on_prev_enable: assert property (
    @(posedge clk) disable iff (reset)
      ($past(enable) && !$past(reset)) |-> (count == $past(count) + 4'd1)
  );

  // With previous no enable and no reset, count holds its value.
  hold_on_prev_disable: assert property (
    @(posedge clk) disable iff (reset)
      (!$past(enable) && !$past(reset)) |-> (count == $past(count))
  );

  // Any change in count must be caused by previous reset or previous enable.
  change_requires_prev_control: assert property (
    @(posedge clk) $changed(count) |-> ($past(reset) || $past(enable))
  );

  // With previous enable and no reset, count must change.
  prev_enable_implies_change: assert property (
    @(posedge clk) disable iff (reset)
      ($past(enable) && !$past(reset)) |-> $changed(count)
  );

  // With previous enable at max value and no reset, wrap to 0 next cycle.
  wrap_on_max: assert property (
    @(posedge clk) disable iff (reset)
      ($past(enable) && !$past(reset) && ($past(count) == 4'hF)) |-> (count == 4'd0)
  );
endmodule