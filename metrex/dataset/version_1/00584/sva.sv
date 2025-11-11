// SVA for binary_counter
// Bind example:
// bind binary_counter binary_counter_sva #(.N(n)) i_binary_counter_sva (.*);

module binary_counter_sva #(parameter int N = 4)
(
  input logic                  clk,
  input logic                  reset,
  input logic                  enable,
  input logic [N-1:0]          count
);

  default clocking cb @(posedge clk); endclocking
  // Disable functional checks during reset; reset-specific checks written explicitly
  default disable iff (reset);

  // No X/Z on controls; count not X/Z when out of reset
  assert property (@cb !$isunknown({reset, enable}));
  assert property (@cb !reset |-> !$isunknown(count));

  // Reset sets and holds count to zero (covers dominance over enable as well)
  assert property (@cb reset |=> count == '0);
  assert property (@cb reset && $past(reset) |=> count == '0);

  // When disabled (and not in reset), count holds
  assert property (@cb !enable |=> count == $past(count));

  // When enabled (and not in reset), count increments modulo 2^N
  assert property (@cb enable |=> count == $past(count) + 1);

  // If count changes (and previous cycle not in reset), the previous enable must have been 1
  assert property (@cb !$past(reset) && $changed(count) |-> $past(enable));

  // Wrap-around on max value when enabled
  assert property (@cb enable && $past(count) == {N{1'b1}} |=> count == '0);

  // Coverage
  cover property (@cb reset ##1 !reset ##1 enable ##1 count == 'd1);                 // reset->count 0, then first increment
  cover property (@cb !reset && !enable ##1 count == $past(count));                  // hold behavior observed
  cover property (@cb !reset && enable && $past(count) == {N{1'b1}} ##1 count == 0); // wrap-around event

endmodule