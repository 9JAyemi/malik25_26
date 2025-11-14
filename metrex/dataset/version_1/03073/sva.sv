// SVA for counter
module counter_sva (
  input logic       clk,
  input logic       reset,
  input logic [3:0] count
);
  default clocking cb @(posedge clk); endclocking

  // Sanity/X checks
  a_no_x:           assert property (!$isunknown({reset,count}));

  // Synchronous reset forces zero
  a_sync_reset:     assert property (reset |-> count == 4'd0);

  // Normal increment when staying out of reset
  a_inc:            assert property (!reset && $past(!reset) |-> count == $past(count) + 4'd1);

  // First value after reset deassertion must be 1 (0 -> 1)
  a_rel_to_one:     assert property ($fell(reset) |-> count == 4'd1);

  // Coverage
  c_reset_hi:       cover  property ($rose(reset));
  c_reset_lo:       cover  property ($fell(reset));
  c_wrap:           cover  property (!reset && $past(!reset) && $past(count) == 4'hF && count == 4'd0);

  sequence no_rst_16; !reset[*16]; endsequence
  c_full_cycle:     cover  property (no_rst_16 ##0 (count == $past(count,16)));

endmodule

bind counter counter_sva u_counter_sva (.clk(clk), .reset(reset), .count(count));