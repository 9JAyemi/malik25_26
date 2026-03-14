module output_signal_module_sva (
  input logic        clk,
  input logic        reset,           // active-low asynchronous reset
  input logic [15:0] input_signal,
  input logic [3:0]  output_signal
);
  ///// Reset behavior /////
  // When reset is asserted LOW, output must be 0.
  check_reset_low_forces_zero: assert property (
    @(posedge clk) (!reset) |-> (output_signal == 4'b0)
  );
  // On falling edge of reset, output must be 0 in the same sampled cycle.
  check_reset_fall_forces_zero: assert property (
    @(posedge clk) $fell(reset) |-> (output_signal == 4'b0)
  );

  ///// Sequential capture of upper nibble /////
  // Out of reset for two cycles: output equals previous cycle's input[15:12].
  check_capture_prev_cycle_nibble: assert property (
    @(posedge clk) disable iff (!reset)
      (reset && $past(reset)) |-> (output_signal == $past(input_signal[15:12]))
  );
  // Bit mapping: output[3] captures previous input_signal[15].
  check_bit3_map_prev15: assert property (
    @(posedge clk) disable iff (!reset)
      (reset && $past(reset)) |-> (output_signal[3] == $past(input_signal[15]))
  );
  // Bit mapping: output[2] captures previous input_signal[14].
  check_bit2_map_prev14: assert property (
    @(posedge clk) disable iff (!reset)
      (reset && $past(reset)) |-> (output_signal[2] == $past(input_signal[14]))
  );
  // Bit mapping: output[1] captures previous input_signal[13].
  check_bit1_map_prev13: assert property (
    @(posedge clk) disable iff (!reset)
      (reset && $past(reset)) |-> (output_signal[1] == $past(input_signal[13]))
  );
  // Bit mapping: output[0] captures previous input_signal[12].
  check_bit0_map_prev12: assert property (
    @(posedge clk) disable iff (!reset)
      (reset && $past(reset)) |-> (output_signal[0] == $past(input_signal[12]))
  );

  ///// Stability and change relations /////
  // If high nibble was stable over the last two cycles (and out of reset), output holds its previous value.
  check_output_stable_when_nibble_stable: assert property (
    @(posedge clk) disable iff (!reset)
      (reset && $past(reset) && $past(reset,2) &&
       ($past(input_signal[15:12]) == $past(input_signal[15:12],2)))
      |-> (output_signal == $past(output_signal))
  );
  // If output changed since last cycle (and out of reset), then the prior two-cycle nibbles differed.
  check_output_change_implies_nibble_change: assert property (
    @(posedge clk) disable iff (!reset)
      (reset && $past(reset) && $past(reset,2) &&
       (output_signal != $past(output_signal)))
      |-> ($past(input_signal[15:12]) != $past(input_signal[15:12],2))
  );
  // If the prior two-cycle nibbles differed (and out of reset), output must change this cycle.
  check_nibble_change_implies_output_change: assert property (
    @(posedge clk) disable iff (!reset)
      (reset && $past(reset) && $past(reset,2) &&
       ($past(input_signal[15:12]) != $past(input_signal[15:12],2)))
      |-> (output_signal != $past(output_signal))
  );
endmodule