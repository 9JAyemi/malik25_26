// SVA for counter_4bit
// Bind this to the DUT:  bind counter_4bit counter_4bit_sva i_counter_4bit_sva(.clk(clk), .reset(reset), .count(count));

module counter_4bit_sva(input logic clk, reset, input logic [3:0] count);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  a_no_x_on_reset:            assert property (@cb !$isunknown(reset));
  a_no_x_on_count_when_run:   assert property (@cb reset |-> !$isunknown(count));

  // Asynchronous, active-low reset drives count to 0 immediately (NBA-safe sampling)
  a_async_reset_to_zero:      assert property (@(negedge reset) ##0 (count == 4'd0 && !$isunknown(count)));

  // While reset is low, sampled on clk, count must be 0
  a_hold_zero_when_reset_low: assert property (@cb !reset |-> count == 4'd0);

  // When reset is high and stable across the cycle, increment by 1 modulo-16
  a_inc_when_reset_stable:    assert property (@cb (reset && $stable(reset)) |-> count == $past(count) + 4'd1);

  // First value after reset release (previous cycle had reset low) must be 1
  a_first_after_release_is_1: assert property (@cb (reset && !$past(reset)) |-> count == 4'd1);

  // Coverage
  c_wrap_15_to_0:   cover property (@cb reset && $stable(reset) && $past(reset) &&
                                     $past(count)==4'hF ##1 count==4'h0);

  c_inc_0_1_2:      cover property (@cb reset && $stable(reset) && $past(reset) &&
                                     $past(count)==4'd0 ##1 count==4'd1 ##1 count==4'd2);

  c_reset_release:  cover property (@cb !$past(reset) && reset && count==4'd1);

endmodule