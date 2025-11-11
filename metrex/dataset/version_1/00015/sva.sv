// SVA for counter: concise, high-quality checks and coverage
module counter_sva(input logic clk, reset, input logic [3:0] count);

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Sanity: no X/Z on key signals after first tick
  a_no_x: assert property (past_valid |-> !$isunknown(reset) && !$isunknown(count));

  // Exact next-state relation (synchronous reset, increment with wrap)
  a_next: assert property (past_valid |->
                           count == ( $past(reset) ? 4'h0
                                                    : ($past(count)==4'hF ? 4'h0
                                                                          : $past(count)+4'h1) ));

  // While reset is held across cycles, count remains 0
  a_hold_reset: assert property (past_valid && reset && $past(reset) |-> count == 4'h0);

  // Coverage
  c_reset_assert:  cover property ($rose(reset));
  c_reset_release: cover property ($fell(reset));
  c_inc:           cover property (past_valid && !$past(reset) && !reset &&
                                   $past(count)!=4'hF && count == $past(count)+4'h1);
  c_wrap:          cover property (past_valid && !$past(reset) && !reset &&
                                   $past(count)==4'hF && count == 4'h0);

endmodule

bind counter counter_sva u_counter_sva(.clk(clk), .reset(reset), .count(count));