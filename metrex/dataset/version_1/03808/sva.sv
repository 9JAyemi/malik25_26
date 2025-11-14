// Assertions and coverage for signal_combiner
module signal_combiner_sva (
  input  logic [3:0] input_signals,
  input  logic       output_signal
);
  logic pair0, pair1, parity;

  always_comb begin
    pair0  = input_signals[0] ^ input_signals[1];
    pair1  = input_signals[2] ^ input_signals[3];
    parity = pair0 ^ pair1;

    // Functional correctness (4-state exact)
    assert (output_signal === parity)
      else $error("signal_combiner: out != (in0^in1)^(in2^in3). in=%b out=%b", input_signals, output_signal);

    assert (output_signal === (^input_signals))
      else $error("signal_combiner: out != ^input_signals. in=%b out=%b", input_signals, output_signal);

    // No spurious X when inputs are known
    assert (!$isunknown(input_signals) ? !$isunknown(output_signal) : 1'b1)
      else $error("signal_combiner: out is X with known inputs. in=%b out=%b", input_signals, output_signal);

    // Parity outcome coverage (odd/even)
    cover (! $isunknown(input_signals) && ((^input_signals) === 1'b0));
    cover (! $isunknown(input_signals) && ((^input_signals) === 1'b1));

    // Pairwise XOR combinations coverage
    cover (! $isunknown(input_signals) && {pair1,pair0} == 2'b00);
    cover (! $isunknown(input_signals) && {pair1,pair0} == 2'b01);
    cover (! $isunknown(input_signals) && {pair1,pair0} == 2'b10);
    cover (! $isunknown(input_signals) && {pair1,pair0} == 2'b11);

    // Population count coverage (0..4 ones)
    int unsigned pop = input_signals[0] + input_signals[1] + input_signals[2] + input_signals[3];
    cover (! $isunknown(input_signals) && pop == 0);
    cover (! $isunknown(input_signals) && pop == 1);
    cover (! $isunknown(input_signals) && pop == 2);
    cover (! $isunknown(input_signals) && pop == 3);
    cover (! $isunknown(input_signals) && pop == 4);

    // Per-bit 0/1 observation coverage
    foreach (input_signals[i]) begin
      cover (! $isunknown(input_signals[i]) && input_signals[i] == 1'b0);
      cover (! $isunknown(input_signals[i]) && input_signals[i] == 1'b1);
    end
  end
endmodule

// Bind into DUT
bind signal_combiner signal_combiner_sva u_signal_combiner_sva (.*);