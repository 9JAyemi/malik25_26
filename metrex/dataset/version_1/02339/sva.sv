// SVA for debouncer
// Bindable checker that verifies key behaviors and provides concise coverage.

`ifndef DEBOUNCER_SVA_SV
`define DEBOUNCER_SVA_SV

module debouncer_sva #(
  parameter int debounce_time = 10
) (
  input  logic                        clock,
  input  logic                        signal_in,
  input  logic                        signal_out,
  input  logic [debounce_time-1:0]    stable_count
);

  localparam int N = debounce_time;

  default clocking cb @(posedge clock); endclocking
  default disable iff ($isunknown({signal_in, signal_out, stable_count}));

  // Output follows an input/output mismatch with 1-cycle latency
  a_follow_change: assert property (signal_in != signal_out |=> signal_out == $past(signal_in));

  // No spurious output changes when input equals output (holds across the next sample)
  a_equal_hold:    assert property (signal_in == signal_out |=> signal_out == $past(signal_out));

  // Counter increments by 1 when input equals output and threshold not reached
  a_count_inc:     assert property (signal_in == signal_out && stable_count != N
                                    |=> stable_count == $past(stable_count)+1);

  // Counter resets at threshold; output value does not change (remains equal)
  a_count_threshold_reset: assert property (signal_in == signal_out && stable_count == N
                                            |=> stable_count == 0 && signal_out == $past(signal_out));

  // Counter resets on any input/output mismatch
  a_count_reset_on_mismatch: assert property (signal_in != signal_out |=> stable_count == 0);

  // Counter never exceeds the threshold value
  a_count_bounded: assert property (stable_count <= N);

  // Output only changes to the previous input value (no other causes)
  a_no_spurious_output_change: assert property ($changed(signal_out)
                                               |-> ($past(signal_in) != $past(signal_out) &&
                                                    signal_out == $past(signal_in)));

  // Coverage

  // Output tracks a change on the next cycle
  c_follow_change: cover property (signal_in != signal_out ##1 signal_out == $past(signal_in));

  // Counter reaches threshold then resets
  c_threshold_then_reset: cover property (stable_count == N ##1 stable_count == 0);

  // Long equal stretch (>= N+1 cycles)
  c_long_equal_stretch: cover property ((signal_in == signal_out)[*N+1]);

  // Mismatch resets counter
  c_mismatch_resets: cover property (signal_in != signal_out ##1 stable_count == 0);

endmodule

// Bind into DUT
bind debouncer debouncer_sva #(.debounce_time(debounce_time)) debouncer_sva_i (
  .clock(clock),
  .signal_in(signal_in),
  .signal_out(signal_out),
  .stable_count(stable_count)
);

`endif