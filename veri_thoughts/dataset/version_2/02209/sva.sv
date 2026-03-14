module register_sva (
  input logic clk,
  input logic reset,
  input logic enable,
  input logic [31:0] data_in,
  input logic [31:0] data_out
);
  // On reset, next cycle data_out is zero.
  reset_clears_output_next: assert property (
    @(posedge clk) reset |=> (data_out == 32'd0)
  );

  // While reset stays asserted, data_out remains zero.
  hold_zero_during_reset: assert property (
    @(posedge clk) (reset && $past(reset)) |-> (data_out == 32'd0)
  );

  // When enabled (and not in reset), next data_out equals prior data_in.
  enable_loads_input_next: assert property (
    @(posedge clk) disable iff (reset) enable |=> (data_out == $past(data_in))
  );

  // When disabled (and not in reset), next data_out holds prior value.
  hold_value_when_disabled: assert property (
    @(posedge clk) disable iff (reset) !enable |=> (data_out == $past(data_out))
  );

  // Reset has priority over enable when both were high previously.
  reset_overrides_enable: assert property (
    @(posedge clk) $past(reset && enable) |-> (data_out == 32'd0)
  );

  // Any change in data_out must be due to prior reset or prior enable.
  change_requires_enable_or_reset: assert property (
    @(posedge clk) (data_out != $past(data_out)) |-> ($past(enable) || $past(reset))
  );

  // If prior cycle was not in reset, next data_out follows enable mux of prior values.
  update_rule_when_no_prior_reset: assert property (
    @(posedge clk) disable iff (reset) (!$past(reset)) |-> (data_out == ($past(enable) ? $past(data_in) : $past(data_out)))
  );

  // After reset deasserts, if enable is low, output remains zero.
  after_reset_zero_if_disabled: assert property (
    @(posedge clk) ($past(reset) && !reset && !enable) |-> (data_out == 32'd0)
  );

  // Two-cycle hold when disabled continuously (and not in reset).
  two_cycle_hold_when_disabled: assert property (
    @(posedge clk) disable iff (reset) (!enable ##1 !enable) |-> (data_out == $past(data_out, 2))
  );

  // With enable asserted in back-to-back cycles (no reset), output follows the second cycle's input.
  two_consecutive_enables_pipeline: assert property (
    @(posedge clk) disable iff (reset) (enable ##1 enable) |-> (data_out == $past(data_in, 1))
  );
endmodule