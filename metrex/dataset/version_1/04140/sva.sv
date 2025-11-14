// SVA for simple_counter
module simple_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // Make $past safe
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Sanity: no X/Z on key signals
  assert property (!$isunknown(reset));
  assert property (!$isunknown(count));

  // Reset behavior: cycle after reset-high, count is 0
  assert property ($past(reset) |-> count == 8'h00);

  // Hold in reset: if reset is held, count stays 0
  assert property (reset && $past(reset) |-> count == 8'h00);

  // Normal update: increment or wrap when not in reset (based on prior cycle)
  assert property (
    !$past(reset) |-> count == (($past(count) == 8'hFF) ? 8'h00 : $past(count) + 1)
  );

  // Coverage: observe wrap 0xFE -> 0xFF -> 0x00 with no reset
  cover property (!reset && count == 8'hFE ##1 !reset && count == 8'hFF ##1 !reset && count == 8'h00);

  // Coverage: observe a normal increment (0x00 -> 0x01) with no reset
  cover property (!reset && count == 8'h00 ##1 !reset && count == 8'h01);

endmodule

bind simple_counter simple_counter_sva u_sva(.clk(clk), .reset(reset), .count(count));