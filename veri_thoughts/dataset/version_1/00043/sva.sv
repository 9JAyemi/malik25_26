// SVA for module counter
// Bind into each counter instance
module counter_sva #(parameter int P_DECR = 1)
(
  input logic        clock,
  input logic        reset,
  input logic        enable,
  input logic [$bits(input_value)-1:0] input_value,
  input logic [$bits(output_value)-1:0] output_value
);
  localparam int W = $bits(output_value);
  localparam logic [W-1:0] DECR = P_DECR[W-1:0];

  default clocking cb @(posedge clock); endclocking

  // Synchronous reset dominates
  assert property (reset |=> output_value == '0);

  // Disable other checks while in reset
  default disable iff (reset)

  // Hold when disabled
  assert property (!enable |=> output_value == $past(output_value));

  // Update when enabled
  assert property (enable |=> output_value == ($past(input_value) - DECR));

  // Any change must be caused by prior enable or prior reset
  assert property ((output_value != $past(output_value)) |-> ($past(enable) || $past(reset)));

  // Knownness
  assert property (!$isunknown(output_value));
  assert property (!$isunknown(input_value) or !enable);

  // Cover: see reset, update, hold, wrap, exact-to-zero
  cover property (reset);
  cover property (enable && !$past(reset));
  cover property (!enable && !$past(reset));
  cover property (enable && !$past(reset) && ($past(input_value) < DECR));
  cover property (enable && !$past(reset) && ($past(input_value) == DECR));

endmodule

bind counter counter_sva #(.P_DECR(DECREMENT_VALUE)) counter_sva_i (.*);