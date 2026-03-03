// SVA for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // Async reset clears immediately
  assert property (@(posedge reset) ##0 (count == 4'd0));

  // While reset is asserted at a clk edge, count is 0
  assert property (reset |-> (count == 4'd0));

  // No X/Z on key signals at clk edge
  assert property (!$isunknown({reset, count}));

  // Increment by 1 each cycle when not in reset (mod-16)
  assert property (disable iff (reset)
                   (!$isunknown($past(count))) |-> (count == $past(count) + 4'd1));

  // Explicit wrap check F -> 0
  assert property (disable iff (reset)
                   ($past(count) == 4'hF) |-> (count == 4'd0));

  // Coverage: full 16-count wrap (0 -> 0 in exactly 16 cycles) without reset
  cover property (disable iff (reset) (count == 4'd0) ##16 (count == 4'd0));

  // Coverage: reset release leads to 1 on next clk
  cover property ($past(reset) && !reset && (count == 4'd1));

endmodule

bind binary_counter binary_counter_sva sva_i(.clk(clk), .reset(reset), .count(count));