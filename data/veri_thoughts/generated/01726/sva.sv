module binary_counter_sva (
  input logic clk,
  input logic reset,
  input logic [1:0] count
);
  // Clock: clk (posedge). Reset: reset active-high synchronous.
  // Logic: mixed (sequential count, combinational next_count).
  // Behavior: modulo-4 up-counter 00->01->10->11->00.

  // On reset, count becomes 00 on the next cycle.
  reset_clears_count_next: assert property (
    @(posedge clk) reset |=> (count == 2'b00)
  );

  // If reset held for consecutive cycles, count is 00 in the current cycle.
  reset_held_keeps_zero: assert property (
    @(posedge clk) (reset && $past(reset)) |-> (count == 2'b00)
  );

  // On reset deassertion cycle, count is still 00 before increment.
  deassert_reset_current_zero: assert property (
    @(posedge clk) $fell(reset) |-> (count == 2'b00)
  );

  // One cycle after reset deasserts, count becomes 01.
  deassert_reset_next_one: assert property (
    @(posedge clk) $fell(reset) |=> (count == 2'b01)
  );

  // From 00, next count is 01 when not in reset.
  step_from_00_to_01: assert property (
    @(posedge clk) disable iff (reset) (count == 2'b00) |=> (count == 2'b01)
  );

  // From 01, next count is 10 when not in reset.
  step_from_01_to_10: assert property (
    @(posedge clk) disable iff (reset) (count == 2'b01) |=> (count == 2'b10)
  );

  // From 10, next count is 11 when not in reset.
  step_from_10_to_11: assert property (
    @(posedge clk) disable iff (reset) (count == 2'b10) |=> (count == 2'b11)
  );

  // From 11, next count is 00 when not in reset.
  step_from_11_to_00: assert property (
    @(posedge clk) disable iff (reset) (count == 2'b11) |=> (count == 2'b00)
  );

  // Count changes every cycle when not in reset.
  count_changes_without_reset: assert property (
    @(posedge clk) disable iff (reset) 1'b1 |=> (count != $past(count))
  );

  // After 4 cycles without reset, count returns to the same value.
  period_four_cycle: assert property (
    @(posedge clk) disable iff (reset) 1'b1 |=> ##4 (count == $past(count,4))
  );
endmodule