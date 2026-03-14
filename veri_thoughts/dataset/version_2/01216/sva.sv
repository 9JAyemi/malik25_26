module counter_sva (
  input logic clk,
  input logic rst,
  input logic dir,
  input logic [7:0] count
);

  // While reset is asserted, count must be 0.
  check_reset_forces_zero: assert property (
    @(posedge clk) rst |-> (count == 8'd0)
  );

  // When dir=1 and count is not 255, next count increments by 1.
  check_up_increments_when_not_max: assert property (
    @(posedge clk) disable iff (rst) (dir && (count != 8'd255)) |=> (count == $past(count) + 8'd1)
  );

  // When dir=1 and count is 255, next count wraps to 0.
  check_up_wraps_at_255: assert property (
    @(posedge clk) disable iff (rst) (dir && (count == 8'd255)) |=> (count == 8'd0)
  );

  // When dir=0 and count is not 0, next count decrements by 1.
  check_down_decrements_when_not_min: assert property (
    @(posedge clk) disable iff (rst) (!dir && (count != 8'd0)) |=> (count == $past(count) - 8'd1)
  );

  // When dir=0 and count is 0, next count wraps to 255.
  check_down_wraps_at_0: assert property (
    @(posedge clk) disable iff (rst) (!dir && (count == 8'd0)) |=> (count == 8'd255)
  );

  // Out of reset, count changes every cycle.
  check_count_changes_each_cycle: assert property (
    @(posedge clk) disable iff (rst) 1'b1 |=> (count != $past(count))
  );

  // Out of reset, LSB toggles every cycle (±1 update).
  check_lsb_toggles_each_cycle: assert property (
    @(posedge clk) disable iff (rst) 1'b1 |=> (count[0] != $past(count[0]))
  );

  // Full next-state equation for dir=1 (increment with wrap at 255).
  check_up_next_state_equation: assert property (
    @(posedge clk) disable iff (rst) dir |-> (count == (($past(count) == 8'd255) ? 8'd0 : ($past(count) + 8'd1)))
  );

  // Full next-state equation for dir=0 (decrement with wrap at 0).
  check_down_next_state_equation: assert property (
    @(posedge clk) disable iff (rst) !dir |-> (count == (($past(count) == 8'd0) ? 8'd255 : ($past(count) - 8'd1)))
  );

  // Step size is always ±1 modulo 256 out of reset.
  check_step_is_plus_or_minus_one: assert property (
    @(posedge clk) disable iff (rst) 1'b1 |=> ((count == $past(count) + 8'd1) || (count == $past(count) - 8'd1))
  );

endmodule