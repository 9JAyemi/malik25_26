// SVA for binary_counter
module binary_counter_sva(
  input logic        clk,
  input logic        reset,
  input logic [3:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Well-formedness
  a_reset_known:         assert property (!$isunknown(reset));
  a_count_known_active:  assert property (!reset |-> !$isunknown(count));
  a_count_in_range:      assert property (!$isunknown(count) |-> count inside {[4'h0:4'hF]});

  // Asynchronous reset takes effect immediately and holds count at 0
  a_async_reset_immediate: assert property (@(posedge reset) count == 4'h0);
  a_reset_forces_zero:     assert property (reset |-> count == 4'h0);
  a_reset_stable:          assert property (reset && $past(reset) |-> $stable(count));

  // Increment-by-1 with wrap when not in reset now and last cycle
  a_inc_mod16: assert property (
    !reset && !$past(reset) |-> ((count == $past(count)+1) || ($past(count)==4'hF && count==4'h0))
  );

  // First clock after synchronous reset release yields 1
  a_post_reset_one: assert property ($fell(reset) |-> count == 4'h1);

  // Coverage
  c_saw_reset:   cover property ($rose(reset));
  c_wrap:        cover property (!reset && !$past(reset) && $past(count)==4'hF && count==4'h0);
  c_full_cycle:  cover property (disable iff (reset) (count==4'h0) ##[1:16] (count==4'hF) ##1 (count==4'h0));
endmodule

bind binary_counter binary_counter_sva i_binary_counter_sva(.clk(clk), .reset(reset), .count(count));