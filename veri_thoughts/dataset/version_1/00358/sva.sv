// SVA for counter. Focused, high-quality checks and coverage.
// Bind this to the DUT instance.

module counter_sva(input logic clk, reset, input logic [7:0] count);
  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on key signals
  a_no_x_reset: assert property (!$isunknown(reset));
  a_no_x_count: assert property (!$isunknown(count));

  // Reset drives zero by the next sampled clock
  a_reset_clears: assert property (reset |=> count == 8'h00);

  // Core next-state function (uses previous count and current reset)
  // Skips first cycle where $past is not valid.
  a_next_state: assert property (
    !$isunknown($past(count)) |->
      count == (reset ? 8'h00 :
                   ($past(count) == 8'hFF ? 8'h00 : $past(count) + 8'h01))
  );

  // Periodic behavior: with 256 consecutive non-reset clocks, value repeats
  a_period_256: assert property ( (!reset)[*256] |-> count == $past(count,256) );

  // Coverage
  c_seen_reset:      cover property (reset);
  c_wrap_event:      cover property (!$past(reset) && !reset && $past(count)==8'hFF && count==8'h00);
  c_inc_0_to_2:      cover property (disable iff (reset) count==8'h00 ##1 count==8'h01 ##1 count==8'h02);
  c_after_reset_inc: cover property (reset ##1 !reset ##1 count==8'h01);
endmodule

bind counter counter_sva u_counter_sva(.clk(clk), .reset(reset), .count(count));