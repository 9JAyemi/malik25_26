module signal_combiner_sva (
    input logic       clk,
    input logic [3:0] input_signals,
    input logic       output_signal
);

    // Output matches the XOR tree implemented in the RTL.
    check_output_matches_xor_tree: assert property (
        @(posedge clk)
        output_signal == ((input_signals[0] ^ input_signals[1]) ^ (input_signals[2] ^ input_signals[3]))
    );

    // Output is the parity of all four input bits.
    check_output_matches_reduction_xor: assert property (
        @(posedge clk)
        output_signal == ^input_signals
    );

    // If the lower pair XOR is 0, the output equals the upper pair XOR.
    check_lower_pair_equal_passes_upper_pair: assert property (
        @(posedge clk)
        ((input_signals[0] ^ input_signals[1]) == 1'b0) |-> (output_signal == (input_signals[2] ^ input_signals[3]))
    );

    // If the lower pair XOR is 1, the output is the inverse of the upper pair XOR.
    check_lower_pair_diff_flips_upper_pair: assert property (
        @(posedge clk)
        ((input_signals[0] ^ input_signals[1]) == 1'b1) |-> (output_signal == ~(input_signals[2] ^ input_signals[3]))
    );

    // If the upper pair XOR is 0, the output equals the lower pair XOR.
    check_upper_pair_equal_passes_lower_pair: assert property (
        @(posedge clk)
        ((input_signals[2] ^ input_signals[3]) == 1'b0) |-> (output_signal == (input_signals[0] ^ input_signals[1]))
    );

    // If the upper pair XOR is 1, the output is the inverse of the lower pair XOR.
    check_upper_pair_diff_flips_lower_pair: assert property (
        @(posedge clk)
        ((input_signals[2] ^ input_signals[3]) == 1'b1) |-> (output_signal == ~(input_signals[0] ^ input_signals[1]))
    );

    // Equal pair parities force the output low.
    check_matching_pair_parities_drive_zero: assert property (
        @(posedge clk)
        ((input_signals[0] ^ input_signals[1]) == (input_signals[2] ^ input_signals[3])) |-> (output_signal == 1'b0)
    );

    // Different pair parities force the output high.
    check_different_pair_parities_drive_one: assert property (
        @(posedge clk)
        ((input_signals[0] ^ input_signals[1]) != (input_signals[2] ^ input_signals[3])) |-> (output_signal == 1'b1)
    );

endmodule