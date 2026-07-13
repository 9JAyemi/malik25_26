module binary_counter_sva (
  input logic clock,
  input logic reset,
  input logic [3:0] counter_output
);

  // Reset drives counter_output to 0 on the clock edge when reset is 1.
  reset_forces_zero: assert property (
    @(posedge clock) reset |-> (counter_output == 4'd0)
  );

  // Out of reset, counter increments by 1 modulo 16 each cycle.
  increment_mod16_out_of_reset: assert property (
    @(posedge clock) disable iff (reset)
      counter_output == ($past(counter_output) + 4'd1)[3:0]
  );

  // When previous value was 15 and not in reset now, wrap to 0.
  wrap_from_15_to_0: assert property (
    @(posedge clock) disable iff (reset)
      ($past(counter_output) == 4'hF) |-> (counter_output == 4'h0)
  );

  // When previous value was 0 and not in reset now, go to 1.
  increment_from_0_to_1: assert property (
    @(posedge clock) disable iff (reset)
      ($past(counter_output) == 4'h0) |-> (counter_output == 4'h1)
  );

  // First cycle after reset deasserts, counter must be 1.
  post_reset_first_count_is_one: assert property (
    @(posedge clock) disable iff (reset)
      ($past(reset) && !reset) |-> (counter_output == 4'd1)
  );

  // Out of reset for two consecutive cycles, value must change each cycle.
  change_each_cycle_out_of_reset: assert property (
    @(posedge clock) disable iff (reset)
      (!$past(reset)) |-> (counter_output != $past(counter_output))
  );

  // If previous value was not 15 and not in reset, current is strictly greater.
  increase_without_wrap: assert property (
    @(posedge clock) disable iff (reset)
      (!$past(reset) && ($past(counter_output) != 4'hF)) |-> (counter_output > $past(counter_output))
  );

  // With two consecutive cycles out of reset, advance by 2 modulo 16 over two cycles.
  two_step_increment_without_reset: assert property (
    @(posedge clock) disable iff (reset)
      (!$past(reset) && !$past(reset,2)) |-> (counter_output == ($past(counter_output,2) + 4'd2)[3:0])
  );

  // LSB toggles every cycle when out of reset.
  lsb_toggles_out_of_reset: assert property (
    @(posedge clock) disable iff (reset)
      counter_output[0] == ~$past(counter_output[0])
  );

  // While reset is held across cycles, counter_output stays 0.
  sustained_reset_holds_zero: assert property (
    @(posedge clock)
      (reset && $past(reset)) |-> (counter_output == 4'd0) && ($past(counter_output) == 4'd0)
  );

endmodule