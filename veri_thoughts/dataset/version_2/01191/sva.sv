module binary_counter_sva (
  input logic clk,
  input logic reset,
  input logic [3:0] count
);
  // Clock: clk (posedge). Reset: reset (synchronous, active-high). Sequential 4-bit up-counter with wrap.

  // Reset high causes count to be 0 on the next clock.
  reset_clears_next: assert property (
    @(posedge clk) reset |=> (count == 4'h0)
  );

  // If reset is held high across consecutive clocks, count is 0.
  reset_held_outputs_zero: assert property (
    @(posedge clk) ($past(reset) && reset) |-> (count == 4'h0)
  );

  // When not in reset for two consecutive clocks, count increments by 1.
  count_increments_when_running: assert property (
    @(posedge clk) disable iff (reset) $past(!reset) |-> (count == $past(count) + 4'd1)
  );

  // When running (no reset in consecutive clocks), count must change.
  count_changes_when_running: assert property (
    @(posedge clk) disable iff (reset) $past(!reset) |-> (count != $past(count))
  );

  // Wrap from 4'hF to 4'h0 on next clock when running.
  wrap_from_f_to_0: assert property (
    @(posedge clk) disable iff (reset) ($past(!reset) && ($past(count) == 4'hF)) |-> (count == 4'h0)
  );

  // On reset deassertion edge, count is 0 in that same cycle.
  deassertion_outputs_zero: assert property (
    @(posedge clk) $fell(reset) |-> (count == 4'h0)
  );

endmodule