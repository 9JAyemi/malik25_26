// SVA for accumulator. Bind to DUT to observe internal prev_sum.
module accumulator_sva #(parameter int n = 8)(
  input logic                  clk,
  input logic                  rst,
  input logic [n-1:0]          data,
  input logic [n-1:0]          sum,
  input logic [n-1:0]          prev_sum
);
  default clocking cb @(posedge clk); endclocking

  // past_valid to safely use $past
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Reset behavior: next cycle both clear to 0
  assert property (rst |=> (sum == '0 && prev_sum == '0));

  // Known values after reset is low
  assert property (disable iff (rst || !past_valid) !$isunknown({sum, prev_sum}));

  // State updates when not in reset
  assert property (disable iff (!past_valid) (!rst) |=> (prev_sum == $past(sum)));
  assert property (disable iff (!past_valid) (!rst) |=> (sum == $past(data) + $past(prev_sum)));

  // Cross-check using only external sum/data across two cycles (no internal dependency)
  assert property (disable iff (!past_valid) (!rst && !$past(rst)) |=> (sum == $past(data) + $past($past(sum))));

  // First cycle after reset deassert: prev_sum was 0, so sum == previous data
  assert property (disable iff (!past_valid) ($past(rst) && !rst) |=> (sum == $past(data)));

  // Functional coverage
  cover property (rst ##1 !rst);                                   // reset deassertion seen
  cover property ((!rst) ##1 (!rst));                               // two consecutive accumulate cycles
  cover property ((!rst) |=> ($past(data) != '0) && (sum < $past(prev_sum))); // wrap-around observed
endmodule

// Bind into the DUT scope (so prev_sum is visible)
bind accumulator accumulator_sva #(.n(n)) acc_sva_i (
  .clk(clk), .rst(rst), .data(data), .sum(sum), .prev_sum(prev_sum)
);