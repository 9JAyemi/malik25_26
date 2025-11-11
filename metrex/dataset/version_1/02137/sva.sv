// SVA for binary_counter
module binary_counter_sva(
  input logic clk, reset, enable,
  input logic [3:0] q
);
  default clocking cb @(posedge clk); endclocking

  // Guard for $past()
  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Sanity: no X on key signals once out of reset
  assert property (disable iff (!past_valid) !reset |-> (!$isunknown(enable) && !$isunknown(q)));

  // Reset behavior
  assert property (reset |-> (q == 4'd0));
  assert property ($fell(reset) |-> (q == 4'd0));

  // Hold when disabled
  assert property (disable iff (reset || !past_valid) !enable |-> (q == $past(q)));

  // Increment when enabled (mod-16 wrap naturally covered)
  assert property (disable iff (reset || !past_valid) enable |-> (q == $past(q) + 4'd1));

  // Coverage
  cover property ($rose(reset));
  cover property ($fell(reset));
  cover property (disable iff (reset || !past_valid) enable && (q == $past(q) + 4'd1));
  cover property (disable iff (reset || !past_valid) !enable && (q == $past(q)));
  cover property (disable iff (reset || !past_valid) ($past(q) == 4'hF && enable && q == 4'h0));
endmodule

bind binary_counter binary_counter_sva sva(.clk(clk), .reset(reset), .enable(enable), .q(q));