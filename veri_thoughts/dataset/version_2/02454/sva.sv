module capture_transition_sva (
  input logic clk,
  input logic reset,            // active-high synchronous reset
  input logic [31:0] input_vector,
  input logic [31:0] output_vector
);

  ///// Reset behavior /////
  // Output is zero whenever reset is asserted.
  reset_outputs_zero: assert property (
    @(posedge clk) reset |-> (output_vector == 32'h0)
  );

  ///// Functional checks /////
  // Output never overlaps current input (output bits imply current input bits are 0).
  output_masked_by_current_input: assert property (
    @(posedge clk) disable iff (reset) ((output_vector & input_vector) == 32'h0)
  );

  // First cycle after leaving reset, output is zero.
  post_reset_first_cycle_output_zero: assert property (
    @(posedge clk) disable iff (reset) ($past(1'b1) && $past(reset) && !reset) |-> (output_vector == 32'h0)
  );

  // When not in reset previously, output equals (~current_input) & previous_input.
  output_matches_fall_mask: assert property (
    @(posedge clk) disable iff (reset) ($past(1'b1) && !$past(reset)) |-> (output_vector == ((~input_vector) & $past(input_vector)))
  );

  // When not in reset previously, any output bit implies that bit of previous input was 1.
  output_requires_prev_input_one: assert property (
    @(posedge clk) disable iff (reset) ($past(1'b1) && !$past(reset)) |-> ((output_vector & ~($past(input_vector))) == 32'h0)
  );

  // Output pulses are at most one cycle wide per bit.
  no_persistent_output_pulses: assert property (
    @(posedge clk) disable iff (reset) ($past(1'b1)) |-> ((output_vector & $past(output_vector)) == 32'h0)
  );

  // If input is unchanged from previous cycle (and not in reset previously), output is zero.
  no_output_when_input_unchanged: assert property (
    @(posedge clk) disable iff (reset) ($past(1'b1) && !$past(reset) && (input_vector == $past(input_vector))) |-> (output_vector == 32'h0)
  );

  // If there are no 1->0 transitions this cycle (and not in reset previously), output is zero.
  no_fall_no_output: assert property (
    @(posedge clk) disable iff (reset) ($past(1'b1) && !$past(reset) && (((~input_vector) & $past(input_vector)) == 32'h0)) |-> (output_vector == 32'h0)
  );

endmodule