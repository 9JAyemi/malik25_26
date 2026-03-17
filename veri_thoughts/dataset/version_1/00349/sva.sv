module xor3_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic y
);

    // y must equal the XOR of all three inputs.
    check_output_matches_three_input_xor: assert property (
        @($global_clock) y == (a ^ b ^ c)
    );

    // When all inputs are low, y must be low.
    check_all_zero_drives_low: assert property (
        @($global_clock) (!a && !b && !c) |-> !y
    );

    // When exactly one input is high, y must be high.
    check_one_hot_drives_high: assert property (
        @($global_clock) ((a && !b && !c) || (!a && b && !c) || (!a && !b && c)) |-> y
    );

    // When exactly two inputs are high, y must be low.
    check_two_hot_drives_low: assert property (
        @($global_clock) ((a && b && !c) || (a && !b && c) || (!a && b && c)) |-> !y
    );

    // When all inputs are high, y must be high.
    check_all_one_drives_high: assert property (
        @($global_clock) (a && b && c) |-> y
    );

endmodule