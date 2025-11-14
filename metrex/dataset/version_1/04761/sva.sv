// SVA for counter
module counter_sva(input clk, input rst, input [3:0] count);
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Reset behavior
  a_reset_sets_zero:         assert property (rst |=> count == 4'd0);
  a_hold_zero_while_reset:   assert property (past_valid && rst && $past(rst) |-> count == 4'd0);

  // Normal operation: increment by 1 (mod-16) when not in reset
  a_inc_by_1:                assert property (past_valid && !rst |=> count == $past(count) + 4'd1);

  // Explicit wrap check from 15 -> 0 when not in reset
  a_wrap_15_to_0:            assert property (past_valid && !rst && $past(!rst) && $past(count)==4'hF |=> count==4'd0);

  // After reset release, first post-release state becomes 1
  a_first_after_release_is_1:assert property (past_valid && $past(rst) && !rst |=> count == 4'd1);

  // No X/Z on count when out of reset
  a_no_x_out_of_reset:       assert property (!rst |-> !$isunknown(count));

  // Coverage
  c_reset_pulse:             cover property ($rose(rst));
  c_reset_release:           cover property ($fell(rst));
  c_wrap_seen:               cover property (past_valid && !rst && $past(!rst) && $past(count)==4'hF |=> count==4'd0);
  c_full_cycle_after_release:cover property ($fell(rst) ##[1:32] (count==4'hF) ##1 (count==4'd0));
endmodule

bind counter counter_sva u_counter_sva(.clk(clk), .rst(rst), .count(count));