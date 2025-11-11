// SVA for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [2:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity: no X/Z on observable signals at sampled time
  assert property (!$isunknown({reset, count})));

  // Synchronous reset drives count to 0 (observed on the cycle after reset was 1)
  assert property ($past(reset) |-> (count == 3'd0));

  // Increment by exactly 1 modulo 8 when not coming from a reset cycle
  assert property (
    !$past(reset) |-> (count == (($past(count) == 3'd7) ? 3'd0 : ($past(count) + 3'd1)))
  );

  // Optional: monotonic progress (count changes every cycle unless coming from reset)
  assert property (!$past(reset) |-> (count != $past(count)));

  // Functional coverage
  // Visit all 8 states
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : cov_states
      cover property (count == i);
    end
  endgenerate

  // See reset effect followed by first increment
  cover property ($rose(reset) ##1 (count == 3'd0) ##1 (count == 3'd1));

  // See wrap-around from 7 to 0 without intervening reset
  cover property (($past(count) == 3'd7) && !$past(reset) && (count == 3'd0));
endmodule

bind binary_counter binary_counter_sva u_binary_counter_sva (
  .clk   (clk),
  .reset (reset),
  .count (count)
);