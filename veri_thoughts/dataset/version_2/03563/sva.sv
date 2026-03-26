module and_or_gate_sva(
    input logic a,
    input logic b,
    input logic c,
    input logic out
);

    // Output always implements (a & b) | c.
    check_out_matches_function: assert property (
        @($global_clock) out == ((a & b) | c)
    );

    // When c is high, the output must be high.
    check_c_high_forces_out_high: assert property (
        @($global_clock) c |-> out
    );

    // When both a and b are high, the output must be high.
    check_a_and_b_high_force_out_high: assert property (
        @($global_clock) (a && b) |-> out
    );

    // With c low and a low, the output must be low.
    check_c_low_and_a_low_force_out_low: assert property (
        @($global_clock) (!c && !a) |-> !out
    );

    // With c low and b low, the output must be low.
    check_c_low_and_b_low_force_out_low: assert property (
        @($global_clock) (!c && !b) |-> !out
    );

endmodule