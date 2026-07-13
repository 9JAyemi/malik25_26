module sky130_fd_sc_hdll__a2bb2oi_sva (
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

    // No explicit clock or reset; sample combinational behavior on $global_clock.

    // Y matches the implemented A2BB2OI logic function.
    check_y_function: assert property (
        @($global_clock) Y == ((A1_N | A2_N) & ~(B1 & B2))
    );

    // If both A inputs are low, Y must be low.
    check_both_a_low_force_y_low: assert property (
        @($global_clock) (~A1_N & ~A2_N) |-> ~Y
    );

    // If both B inputs are high, Y must be low.
    check_both_b_high_force_y_low: assert property (
        @($global_clock) (B1 & B2) |-> ~Y
    );

    // Y must be high when an A input is high and the B AND term is low.
    check_high_condition_drives_y_high: assert property (
        @($global_clock) ((A1_N | A2_N) & ~(B1 & B2)) |-> Y
    );

    // A high Y requires at least one A input to be high.
    check_y_high_requires_a_input: assert property (
        @($global_clock) Y |-> (A1_N | A2_N)
    );

    // A high Y requires B1 and B2 not to be high together.
    check_y_high_requires_b_and_low: assert property (
        @($global_clock) Y |-> ~(B1 & B2)
    );

    // A low Y must come from both A inputs low or both B inputs high.
    check_y_low_has_valid_cause: assert property (
        @($global_clock) ~Y |-> ((~A1_N & ~A2_N) | (B1 & B2))
    );

endmodule