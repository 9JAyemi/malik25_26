module top_module_sva (
    input logic        clk,
    input logic [99:0] in,
    input logic        out_and,
    input logic        out_or,
    input logic        out_xor
);

    // out_and is the reduction-AND of all input bits.
    check_out_and_matches_reduction_and: assert property (
        @(posedge clk) out_and == (&in)
    );

    // out_or is the reduction-OR of all input bits.
    check_out_or_matches_reduction_or: assert property (
        @(posedge clk) out_or == (|in)
    );

    // out_xor is the reduction-XOR of all input bits.
    check_out_xor_matches_reduction_xor: assert property (
        @(posedge clk) out_xor == (^in)
    );

    // All-zero input drives all three outputs low.
    check_zero_input_drives_zero_outputs: assert property (
        @(posedge clk) (in == 100'b0) |-> ((out_and == 1'b0) && (out_or == 1'b0) && (out_xor == 1'b0))
    );

    // All-one input drives out_and and out_or high and out_xor low.
    check_all_ones_drive_expected_outputs: assert property (
        @(posedge clk) (in == 100'b1) |-> ((out_and == 1'b1) && (out_or == 1'b1) && (out_xor == 1'b0))
    );

    // Equal number of 0s and 1s drives out_xor high.
    check_equal_zero_one_counts_drive_xor_high: assert property (
        @(posedge clk) ((&in) == (|in)) |-> (out_xor == 1'b1)
    );

    // Unequal number of 0s and 1s drives out_xor low.
    check_unequal_zero_one_counts_drive_xor_low: assert property (
        @(posedge clk) ((&in) != (|in)) |-> (out_xor == 1'b0)
    );

    // If out_and is high, at least one input bit must be high.
    check_out_and_high_requires_any_input_high: assert property (
        @(posedge clk) out_and |-> (|in)
    );

    // If out_or is high, at least one input bit must be high.
    check_out_or_high_requires_any_input_high: assert property (
        @(posedge clk) out_or |-> (|in)
    );

    // If out_and is low, all input bits must be low.
    check_out_and_low_requires_all_inputs_low: assert property (
        @(posedge clk) !out_and |-> (~&in)
    );

    // If out_or is low, all input bits must be low.
    check_out_or_low_requires_all_inputs_low: assert property (
        @(posedge clk) !out_or |-> (~|in)
    );

endmodule