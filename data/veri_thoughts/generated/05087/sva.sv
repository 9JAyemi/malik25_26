module power_good_sva (
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

    // Y matches the implemented combinational function.
    check_y_boolean_function: assert property (
        @($global_clock) Y == ((A1_N & A2_N) | (~B1 & ~B2))
    );

    // Both A inputs high force Y high.
    check_a_pair_high_forces_y_high: assert property (
        @($global_clock) (A1_N & A2_N) |-> Y
    );

    // Both B inputs low force Y high.
    check_b_pair_low_forces_y_high: assert property (
        @($global_clock) (~B1 & ~B2) |-> Y
    );

    // Any B high without both A high forces Y low.
    check_b_active_without_a_pair_high_forces_y_low: assert property (
        @($global_clock) ((B1 | B2) & ~(A1_N & A2_N)) |-> ~Y
    );

    // A low Y must be caused by a B high and not both A inputs high.
    check_y_low_has_valid_cause: assert property (
        @($global_clock) (~Y) |-> ((B1 | B2) & ~(A1_N & A2_N))
    );

    // A high Y with any B high requires both A inputs high.
    check_y_high_with_b_active_requires_a_pair_high: assert property (
        @($global_clock) (Y & (B1 | B2)) |-> (A1_N & A2_N)
    );

endmodule