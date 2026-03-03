// SVA for up_counter. Bind this to the DUT.
module up_counter_sva(input logic clk, reset, input logic [3:0] count);

  // Use posedge clk as the assertion clock
  default clocking cb @(posedge clk); endclocking

  // Next-state functional correctness
  // If reset is asserted on this clock, next cycle the counter is 0
  a_reset_next_zero: assert property (reset |=> count == 4'd0);

  // If not in reset on this clock (and we have a known prior value), next cycle increments by 1 (mod 16)
  a_inc_next: assert property ((!reset && !$isunknown($past(count))) |=> count == ($past(count) + 4'd1));

  // Output changes only on clock edges (no mid-cycle glitches)
  a_glitchless: assert property ($changed(count) |-> $rose(clk));

  // After any reset cycle, the output is known (not X/Z) on the next cycle
  a_known_after_reset: assert property ($past(reset) |-> !$isunknown(count));

  // Basic safety: count is always 4-bit known when not in reset (after at least one prior sample)
  a_known_while_running: assert property ((!reset && !$isunknown($past(count))) |-> !$isunknown(count));

  // ---------------------------------
  // Coverage
  // See a reset pulse followed by run
  c_reset_pulse: cover property (reset ##1 !reset);

  // See a normal increment step
  c_inc_step: cover property ($past(!reset) && (count == ($past(count) + 4'd1)));

  // See wrap-around from 0xF to 0x0 while running
  c_wrap: cover property ($past(!reset) && ($past(count) == 4'hF) && (count == 4'h0));

  // See a full 16-step cycle (returns to same value after 16 non-reset clocks)
  c_full_cycle: cover property (!reset [*16] ##0 (count == $past(count,16)));

endmodule

// Bind into the DUT
bind up_counter up_counter_sva u_up_counter_sva(.clk(clk), .reset(reset), .count(count));