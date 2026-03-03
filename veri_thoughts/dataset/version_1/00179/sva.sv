// SVA for up_counter
module up_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [2:0]  count
);
  default clocking @(posedge clk); endclocking

  // Sanity: no X/Z on key signals at sampling
  assert property (!$isunknown({reset, count}));

  // Golden next-state relation (covers reset and increment, incl. wrap)
  assert property ($past_valid |-> count == ($past(reset) ? 3'd0 : $past(count) + 3'd1));

  // While reset is held, counter output stays 0 (after first cycle of reset)
  assert property (reset && $past(reset) |-> count == 3'd0);

  // Cover: single-cycle reset pulse forces next count to 0
  cover property ($rose(reset) ##1 (count == 3'd0));

  // Cover: wrap-around 7 -> 0 with no reset
  cover property ($past_valid && !$past(reset) && !reset && $past(count) == 3'd7 && count == 3'd0);

  // Cover: full 8-count cycle after reset deassertion
  sequence step; !reset && (count == $past(count) + 3'd1); endsequence
  cover property ($fell(reset) ##1 step[*7] ##1 (!reset && count == 3'd0));
endmodule

// Bind into all instances of up_counter
bind up_counter up_counter_sva u_up_counter_sva (.clk(clk), .reset(reset), .count(count));