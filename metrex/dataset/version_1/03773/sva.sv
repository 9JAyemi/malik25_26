// SVA for sync_counter
module sync_counter_sva (
  input clk,
  input reset,
  input [3:0] count
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  a_inputs_known:  assert property (!$isunknown(reset));
  a_count_known:   assert property (!$isunknown(count));

  // Reset behavior
  a_reset_clears:       assert property (reset |=> count == 4'h0);
  a_reset_holds_zero:   assert property (!$initstate && reset && $past(reset) |-> count == 4'h0);

  // Increment modulo-16 when not in reset
  a_incr: assert property (!$initstate && !$past(reset) && !reset |-> count == $past(count) + 4'd1);

  // Explicit wrap check 15 -> 0
  a_wrap: assert property (!$initstate && !$past(reset) && !reset && $past(count) == 4'hF |-> count == 4'h0);

  // Functional coverage
  c_reset_seen:             cover property (reset);
  c_reset_clears_next:      cover property (reset ##1 count == 4'h0);
  c_post_reset_increment:   cover property (reset ##1 !reset ##1 count == 4'h1);
  c_wrap_covered:           cover property (!$initstate && !$past(reset) && !reset && $past(count) == 4'hF ##1 count == 4'h0);
  c_16_free_running:        cover property (!reset[*16]); // 16 consecutive cycles without reset
endmodule

// Bind into DUT
bind sync_counter sync_counter_sva u_sync_counter_sva (.clk(clk), .reset(reset), .count(count));