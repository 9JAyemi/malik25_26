module binary_counter_sva
#(
  parameter N = 4
)
(
  input logic clk,
  input logic reset,
  input logic [N-1:0] count
);

  // Reset drives count to zero on the next clock.
  check_reset_clears_count: assert property (
    @(posedge clk) reset |=> (count == {N{1'b0}})
  );

  // When not in reset, count increments by one on the next clock.
  check_count_increments: assert property (
    @(posedge clk) disable iff (reset) 1'b1 |=> (count == ($past(count) + 1'b1))
  );

  // When not in reset, count never holds its previous value.
  check_count_never_holds: assert property (
    @(posedge clk) disable iff (reset) 1'b1 |=> (count != $past(count))
  );

  // When not in reset, count wraps from all ones back to zero.
  check_count_wraps: assert property (
    @(posedge clk) disable iff (reset) (count == {N{1'b1}}) |=> (count == {N{1'b0}})
  );

  // If reset is held across consecutive clocks, count remains zero.
  check_reset_held_keeps_zero: assert property (
    @(posedge clk) (reset && $past(reset)) |-> (count == {N{1'b0}})
  );

  // If reset is held across consecutive clocks, count does not increment.
  check_reset_held_no_increment: assert property (
    @(posedge clk) (reset && $past(reset)) |-> (count == $past(count))
  );

endmodule