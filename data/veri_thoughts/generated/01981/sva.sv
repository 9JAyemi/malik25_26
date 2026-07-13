module counter_module_sva (
  input logic clk,
  input logic rst,
  input logic cnt_en,
  input logic [7:0] count
);
  // Clock: clk (posedge). Reset: rst (active-high, async). Sequential counter: increments when cnt_en && count < MAX_COUNT, else clears to 0.
  parameter int unsigned MAX_COUNT = 255;

  // Reset high forces count to zero in the same cycle.
  check_reset_now: assert property (
    @(posedge clk) rst |-> (count == 8'h00)
  );

  // Reset high forces count to zero in the next cycle too.
  check_reset_next: assert property (
    @(posedge clk) rst |=> (count == 8'h00)
  );

  // If enabled and below MAX_COUNT, increment by 1 next cycle.
  check_increment_when_enabled_below_max: assert property (
    @(posedge clk) disable iff (rst) (cnt_en && (count < MAX_COUNT)) |=> (count == $past(count) + 1)
  );

  // If disabled, clear to zero next cycle.
  check_clear_when_disabled: assert property (
    @(posedge clk) disable iff (rst) (!cnt_en) |=> (count == 8'h00)
  );

  // If enabled and at/above MAX_COUNT, clear to zero next cycle.
  check_clear_when_enabled_at_or_above_max: assert property (
    @(posedge clk) disable iff (rst) (cnt_en && (count >= MAX_COUNT)) |=> (count == 8'h00)
  );

  // Incrementing implies the value changes (no stutter).
  check_no_stutter_on_increment: assert property (
    @(posedge clk) disable iff (rst) (cnt_en && (count < MAX_COUNT)) |=> (count != $past(count))
  );

  // From MAX_COUNT-1 with enable, reach MAX_COUNT next cycle.
  check_reach_max_from_max_minus_one: assert property (
    @(posedge clk) disable iff (rst) ($past(cnt_en) && ($past(count) == (MAX_COUNT - 1))) |-> (count == MAX_COUNT)
  );

  // From MAX_COUNT with enable, wrap/clear to zero next cycle.
  check_wrap_to_zero_from_max_enabled: assert property (
    @(posedge clk) disable iff (rst) ($past(cnt_en) && ($past(count) >= MAX_COUNT)) |-> (count == 8'h00)
  );

  // Nonzero count implies prior cycle had enable and count<MAX_COUNT.
  check_nonzero_implies_prev_enable_below_max: assert property (
    @(posedge clk) disable iff (rst) (count != 8'h00) |-> ($past(cnt_en) && ($past(count) < MAX_COUNT))
  );

  // On reset release with enable, go to 1 next cycle.
  check_release_with_enable_goes_to_one: assert property (
    @(posedge clk) $fell(rst) && cnt_en |=> (count == 8'd1)
  );

  // On reset release with disable, stay at 0 next cycle.
  check_release_with_disable_keeps_zero: assert property (
    @(posedge clk) $fell(rst) && !cnt_en |=> (count == 8'h00)
  );

endmodule