module binary_counter_sva (
  input logic clk,
  input logic rst,
  input logic [3:0] count,
  input logic max_reached
);

  // While reset is asserted, outputs are driven to zero.
  reset_drives_zero: assert property (
    @(posedge clk) rst |-> (count == 4'h0) && (max_reached == 1'b0)
  );

  // If previous cycle was active and count != 15, next count increments by 1 and flag is 0.
  increment_when_not_max: assert property (
    @(posedge clk) disable iff (rst)
      ($past(!rst) && ($past(count) != 4'hF)) |-> (count == ($past(count) + 4'd1)) && (max_reached == 1'b0)
  );

  // If previous cycle was active and count == 15, next count wraps to 0 and flag is 1.
  wrap_when_prev_max: assert property (
    @(posedge clk) disable iff (rst)
      ($past(!rst) && ($past(count) == 4'hF)) |-> (count == 4'h0) && (max_reached == 1'b1)
  );

  // Flag can only rise when previous count was 15.
  flag_rise_only_on_wrap: assert property (
    @(posedge clk) disable iff (rst)
      $rose(max_reached) |-> ($past(count) == 4'hF)
  );

  // When flag is 1, count is 0 in the same cycle.
  flag_implies_zero_count: assert property (
    @(posedge clk) disable iff (rst)
      max_reached |-> (count == 4'h0)
  );

  // Flag is a single-cycle pulse.
  flag_one_cycle_pulse: assert property (
    @(posedge clk) disable iff (rst)
      max_reached |-> !max_reached
  );

  // If count is non-zero, flag must be 0.
  nonzero_count_implies_flag_zero: assert property (
    @(posedge clk) disable iff (rst)
      (count != 4'h0) |-> (max_reached == 1'b0)
  );

  // If previous cycle was active and current count is 0, previous count was 15.
  zero_now_means_prev_max: assert property (
    @(posedge clk) disable iff (rst)
      ($past(!rst) && (count == 4'h0)) |-> ($past(count) == 4'hF)
  );

  // In active operation, count changes every cycle (increments or wraps).
  count_changes_every_cycle_active: assert property (
    @(posedge clk) disable iff (rst)
      $past(!rst) |-> (count != $past(count))
  );

  // If current count is 15, next cycle wraps to 0 and flag is 1.
  present_max_wraps_next: assert property (
    @(posedge clk) disable iff (rst)
      (count == 4'hF) |-> ##1 (count == 4'h0) && (max_reached == 1'b1)
  );

endmodule