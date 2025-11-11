// SVA for binary_counter
module binary_counter_sva(
  input logic       clk,
  input logic       reset,
  input logic       enable,
  input logic [3:0] count
);
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always @(cb) past_valid <= 1'b1;

  // Functional correctness
  a_reset_clears:           assert property (reset |-> count == 4'd0);
  a_hold_when_disabled:     assert property (past_valid && !reset && !enable |-> $stable(count));
  a_inc_when_enabled:       assert property (past_valid && !reset &&  enable |-> count == $past(count) + 4'd1);
  a_wrap_check:             assert property (past_valid && !reset &&  enable && $past(count)==4'hF |-> count==4'h0);
  a_no_x_after_reset:       assert property (past_valid && !reset |-> !$isunknown(count));

  // Reset-release corner cases
  a_post_reset_hold:        assert property (past_valid && $past(reset) && !reset && !enable |-> count==4'd0);
  a_post_reset_first_inc:   assert property (past_valid && $past(reset) && !reset &&  enable |-> count==4'd1);

  // Useful coverage
  c_reset_seen:   cover property (reset);
  c_hold_seen:    cover property (past_valid && !reset && !enable && $stable(count));
  c_inc_seen:     cover property (past_valid && !reset && enable && count == $past(count) + 4'd1);
  c_wrap_seen:    cover property (past_valid && !reset && enable && $past(count)==4'hF && count==4'h0);
  c_full_cycle:   cover property (reset ##1 (!reset && enable)[*16] ##0 (count==4'd0));
endmodule

bind binary_counter binary_counter_sva u_sva (.clk(clk), .reset(reset), .enable(enable), .count(count));