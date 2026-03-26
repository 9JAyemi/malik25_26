module PLA_sva (
    input logic in1,
    input logic in2,
    input logic out1
);

    // out1 matches the RTL Boolean expression.
    check_out1_matches_rtl_expr: assert property (
        @($global_clock) out1 == ((in1 & in2) ^ (in1 | in2))
    );

    // When both inputs are low, out1 is low.
    check_both_inputs_low_drives_low: assert property (
        @($global_clock) (!in1 && !in2) |-> !out1
    );

    // When only in2 is high, out1 is high.
    check_only_in2_high_drives_high: assert property (
        @($global_clock) (!in1 && in2) |-> out1
    );

    // When only in1 is high, out1 is high.
    check_only_in1_high_drives_high: assert property (
        @($global_clock) (in1 && !in2) |-> out1
    );

    // When both inputs are high, out1 is low.
    check_both_inputs_high_drives_low: assert property (
        @($global_clock) (in1 && in2) |-> !out1
    );

    // out1 is high exactly when the inputs differ.
    check_xor_behavior: assert property (
        @($global_clock) out1 == (in1 ^ in2)
    );

endmodule