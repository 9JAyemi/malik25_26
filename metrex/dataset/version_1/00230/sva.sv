// SVA for five_bit_module
module five_bit_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [4:0]  input_signal,
  input logic [4:0]  output_signal
);
  default clocking cb @(posedge clk); endclocking

  // Track first sampled cycle to avoid spurious X-check failures at time 0
  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Reset behavior: next-cycle output must be 0 whenever reset is sampled high
  assert property (reset |=> output_signal == 5'd0);

  // Functional mapping for all non-reset cycles (uses inputs from prior cycle)
  assert property (
    !reset |=> output_signal ==
      (($past(input_signal) == 5'd0) ? 5'd0 :
       ($past(input_signal)[0] == 1'b0) ? ($past(input_signal) + 5'd1) :
                                          ($past(input_signal) - 5'd1))
  );

  // No X/Z on key IOs after first sampled cycle
  assert property (past_valid |-> !$isunknown({reset, input_signal, output_signal}));

  // Coverage: exercise each branch and key boundary values
  cover property (reset ##1 !reset);
  cover property (!reset && input_signal == 5'd0 ##1 output_signal == 5'd0);
  cover property (!reset && input_signal != 5'd0 && input_signal[0] == 1'b0 ##1
                  output_signal == input_signal + 5'd1); // even, non-zero
  cover property (!reset && input_signal[0] == 1'b1 ##1
                  output_signal == input_signal - 5'd1); // odd
  cover property (!reset && input_signal == 5'd30 ##1 output_signal == 5'd31);
  cover property (!reset && input_signal == 5'd31 ##1 output_signal == 5'd30);
  cover property (!reset && input_signal == 5'd1  ##1 output_signal == 5'd0);
endmodule

// Example bind (uncomment to use):
// bind five_bit_module five_bit_module_sva sva (.*);