module top_module_sva (
    input logic [99:0] in,
    input logic out_and,
    input logic out_or,
    input logic out_xor
);

    // out_and is the reduction AND of the top 10 input bits.
    check_out_and_matches_upper_slice: assert property (
        @($global_clock) out_and == (&in[99:90])
    );

    // out_or is the reduction OR of the top 10 input bits.
    check_out_or_matches_upper_slice: assert property (
        @($global_clock) out_or == (|in[99:90])
    );

    // out_xor is the reduction XOR of the top 10 input bits.
    check_out_xor_matches_upper_slice: assert property (
        @($global_clock) out_xor == (^in[99:90])
    );

    // An all-zero top slice drives all outputs low.
    check_all_zero_upper_slice: assert property (
        @($global_clock) (in[99:90] == 10'h000) |-> (!out_and && !out_or && !out_xor)
    );

    // An all-one top slice drives AND and OR high, and XOR low.
    check_all_one_upper_slice: assert property (
        @($global_clock) (in[99:90] == 10'h3FF) |-> (out_and && out_or && !out_xor)
    );

    // A one-hot top slice drives OR and XOR high, and AND low.
    check_onehot_upper_slice: assert property (
        @($global_clock) $onehot(in[99:90]) |-> (!out_and && out_or && out_xor)
    );

    // If out_and is high, out_or must be high and out_xor must be low.
    check_out_and_consistency: assert property (
        @($global_clock) out_and |-> (out_or && !out_xor)
    );

    // If out_xor is high, out_or must be high and out_and must be low.
    check_out_xor_consistency: assert property (
        @($global_clock) out_xor |-> (out_or && !out_and)
    );

    // If out_or is low, the top 10 input bits must all be zero.
    check_out_or_low_means_upper_zero: assert property (
        @($global_clock) !out_or |-> (in[99:90] == 10'h000)
    );

    // If out_and is high, the top 10 input bits must all be one.
    check_out_and_high_means_upper_ones: assert property (
        @($global_clock) out_and |-> (in[99:90] == 10'h3FF)
    );

endmodule