// SVA for signal_combiner
// Place in a separate file and compile with DUT; binding provided below.
// Focuses on correctness, X-cleanliness, parity behavior, and concise coverage.

`ifndef SYNTHESIS
module signal_combiner_sva (
  input logic [3:0] input_signals,
  input logic       output_signal,
  input logic [1:0] input_sum
);

  default clocking cb @(*); endclocking

  // X/Z-clean
  a_no_x: assert property (!$isunknown({input_signals, input_sum, output_signal}));

  // Structural correctness
  a_pair0:  assert property (input_sum[0] == (input_signals[0] ^ input_signals[1]));
  a_pair1:  assert property (input_sum[1] == (input_signals[2] ^ input_signals[3]));
  a_out_xy: assert property (output_signal == (input_sum[0] ^ input_sum[1]));

  // Functional parity equivalence
  a_parity: assert property (output_signal == ^input_signals);

  // Dynamic behavior: output toggles iff an odd number of inputs toggle
  a_change_parity: assert property (
    $changed(output_signal) ==
    ^{$changed(input_signals[0]), $changed(input_signals[1]),
      $changed(input_signals[2]), $changed(input_signals[3])}
  );

  // Coverage: observe output values
  c_out0: cover property (output_signal == 1'b0);
  c_out1: cover property (output_signal == 1'b1);

  // Coverage: all input combinations (full 4-bit space)
  genvar v;
  generate
    for (v = 0; v < 16; v++) begin : C_ALL_INPUTS
      c_all: cover property (input_signals == v[3:0]);
    end
  endgenerate

  // Coverage: number of simultaneous input toggles in a time-step
  c_1chg: cover property (
    ($changed(input_signals[0]) + $changed(input_signals[1]) +
     $changed(input_signals[2]) + $changed(input_signals[3])) == 1
  );
  c_2chg: cover property (
    ($changed(input_signals[0]) + $changed(input_signals[1]) +
     $changed(input_signals[2]) + $changed(input_signals[3])) == 2
  );
  c_3chg: cover property (
    ($changed(input_signals[0]) + $changed(input_signals[1]) +
     $changed(input_signals[2]) + $changed(input_signals[3])) == 3
  );
  c_4chg: cover property (
    ($changed(input_signals[0]) + $changed(input_signals[1]) +
     $changed(input_signals[2]) + $changed(input_signals[3])) == 4
  );

endmodule

// Bind into the DUT to access internal input_sum
bind signal_combiner signal_combiner_sva SVA (
  .input_signals(input_signals),
  .output_signal(output_signal),
  .input_sum    (input_sum)
);
`endif