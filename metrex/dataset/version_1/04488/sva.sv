// SVA for binary_counter
module binary_counter_sva (input clk, input rst_n, input [3:0] count);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity: no X on rst_n/count at clock edges
  assert property (@(cb) !$isunknown({rst_n, count}));

  // Asynchronous reset forces 0 immediately
  assert property (@(negedge rst_n) ##0 (count == 4'd0));

  // While in reset, hold 0 and stay stable at each clk
  assert property (@(cb) !rst_n |-> (count == 4'd0 && $stable(count)));

  // First cycle after reset release: 0 -> 1
  assert property (@(cb) rst_n && !$past(rst_n) |-> ($past(count) == 4'd0 && count == 4'd1));

  // When out of reset, increment by 1 every cycle (wraps mod-16)
  assert property (@(cb) rst_n && $past(rst_n) |-> count == $past(count) + 4'd1);

  // Coverage: reset assertion/deassertion observed
  cover property (@(negedge rst_n));
  cover property (@(posedge rst_n));

  // Coverage: wrap-around F -> 0
  cover property (@(cb) rst_n && $past(rst_n) && ($past(count) == 4'hF) && (count == 4'h0));

  // Coverage: see 16 consecutive correct increments out of reset
  sequence inc_step;
    rst_n && $past(rst_n) && (count == $past(count) + 4'd1);
  endsequence
  cover property (@(cb) inc_step[*16]);

endmodule

bind binary_counter binary_counter_sva i_binary_counter_sva (.clk(clk), .rst_n(rst_n), .count(count));