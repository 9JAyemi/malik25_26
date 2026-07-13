module binary_counter_sva
#(
  parameter N = 4
)
(
  input logic clk,
  input logic reset,
  input logic [N-1:0] count
);

  // A reset cycle drives count to zero by the next clock.
  check_reset_drives_zero: assert property (
    @(posedge clk) reset |=> (count == '0)
  );

  // The first cycle after reset deassertion still observes count at zero.
  check_release_from_reset_zero: assert property (
    @(posedge clk) disable iff (reset)
    !$initstate && $past(reset) |-> (count == '0)
  );

  // In normal operation, a non-maximum count increments by one.
  check_increment_nonmax: assert property (
    @(posedge clk) disable iff (reset)
    !$initstate && !$past(reset) && ($past(count) != {N{1'b1}})
    |-> (count == ($past(count) + 1'b1))
  );

  // In normal operation, the maximum count wraps back to zero.
  check_wrap_from_max: assert property (
    @(posedge clk) disable iff (reset)
    !$initstate && !$past(reset) && ($past(count) == {N{1'b1}})
    |-> (count == '0)
  );

endmodule