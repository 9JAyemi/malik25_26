module test_eval_generic_sva (
    input logic [7:0] data,
    input logic       out_bit_def,
    input logic       out_bit_ovr
);

    // out_bit_ovr mirrors data[4].
    check_out_bit_ovr_matches_data4: assert property (
        @($global_clock) out_bit_ovr == data[4]
    );

    // out_bit_def is high when data[4] is high.
    check_out_bit_def_high_when_data4_high: assert property (
        @($global_clock) data[4] |-> out_bit_def
    );

    // out_bit_def is low when data[4] is low.
    check_out_bit_def_low_when_data4_low: assert property (
        @($global_clock) !data[4] |-> !out_bit_def
    );

    // out_bit_def is high when data has at least four 1 bits.
    check_out_bit_def_high_when_four_or_more_ones: assert property (
        @($global_clock) $countones(data) >= 4 |-> out_bit_def
    );

    // out_bit_def is low when data has fewer than four 1 bits.
    check_out_bit_def_low_when_less_than_four_ones: assert property (
        @($global_clock) $countones(data) < 4 |-> !out_bit_def
    );

    // out_bit_def matches the threshold comparison of data[4] and the one count.
    check_out_bit_def_matches_threshold_logic: assert property (
        @($global_clock) out_bit_def == (data[4] || ($countones(data) >= 4))
    );

    // out_bit_def is high only when data[4] is high or the one count is at least four.
    check_out_bit_def_high_only_for_valid_conditions: assert property (
        @($global_clock) out_bit_def |-> (data[4] || ($countones(data) >= 4))
    );

    // out_bit_def is low only when data[4] is low and the one count is less than four.
    check_out_bit_def_low_only_for_invalid_conditions: assert property (
        @($global_clock) !out_bit_def |-> (!data[4] && ($countones(data) < 4))
    );

endmodule