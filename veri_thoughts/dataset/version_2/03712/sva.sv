module and_wire_sva (
    input logic a,
    input logic b,
    input logic out
);

    // Output must equal the AND of the two inputs.
    check_out_matches_and: assert property (
        @($global_clock) out == (a & b)
    );

    // If a is LOW, the output must be LOW.
    check_a_low_forces_out_low: assert property (
        @($global_clock) !a |-> !out
    );

    // If b is LOW, the output must be LOW.
    check_b_low_forces_out_low: assert property (
        @($global_clock) !b |-> !out
    );

    // If both inputs are HIGH, the output must be HIGH.
    check_both_high_drive_out_high: assert property (
        @($global_clock) (a && b) |-> out
    );

endmodule