// SVA for binary_counter
module binary_counter_sva(input clk, input rst, input [3:0] q);
  default clocking @(posedge clk); endclocking

  // Sanity
  a_no_x:                 assert property (!$isunknown(q));

  // Reset behavior
  a_rst_next_zero:        assert property (rst |=> q == 4'd0);
  a_rst_held_zero:        assert property ($past_valid && $past(rst) && rst |-> q == 4'd0);

  // Increment behavior (incl. wrap), both steady-state and after reset release
  a_inc_normal:           assert property ($past_valid && !rst && !$past(rst) |-> q == $past(q) + 4'd1);
  a_inc_after_release:    assert property ($past_valid && !rst &&  $past(rst) |-> q == $past(q) + 4'd1);

  // Coverage
  c_first_inc_after_rel:  cover  property ($fell(rst) ##1 q == 4'd1);
  c_wrap:                 cover  property ($past_valid && !rst && !$past(rst) && $past(q) == 4'hF && q == 4'h0);
  c_full_cycle_no_reset:  cover  property ($fell(rst) ##1 !rst[*16] ##1 q == 4'd0);
endmodule

bind binary_counter binary_counter_sva sva_inst (.*);