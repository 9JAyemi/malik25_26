// SVA for up_counter
module up_counter_sva (
  input logic        clk,
  input logic        rst,      // active-low async
  input logic [3:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // Async clear must take effect immediately on rst falling edge
  ap_async_clear: assert property (@(negedge rst) count == 4'h0);

  // While in reset, counter holds at 0 on every clk
  ap_hold_in_reset: assert property (!rst |-> count == 4'h0);

  // When running (no reset), increment by 1 each clk (no stall)
  ap_inc_no_wrap: assert property (rst && $past(rst) && ($past(count) != 4'hF) |-> count == ($past(count) + 4'd1));
  ap_wrap:        assert property (rst && $past(rst) && ($past(count) == 4'hF) |-> count == 4'h0);

  // No X/Z on key signals at clk
  ap_known: assert property (!$isunknown({rst, count}));

  // Coverage: async reset observed
  cp_async_reset: cover property (@(negedge rst) 1'b1);

  // Coverage: deassert reset then see first increment to 1
  cp_first_inc: cover property (!rst ##1 rst ##1 count == 4'h1);

  // Coverage: wraparound F -> 0
  cp_wrap: cover property (disable iff (!rst) (count == 4'hE) ##1 (count == 4'hF) ##1 (count == 4'h0));

endmodule

// Bind into DUT
bind up_counter up_counter_sva u_up_counter_sva(.clk(clk), .rst(rst), .count(count));