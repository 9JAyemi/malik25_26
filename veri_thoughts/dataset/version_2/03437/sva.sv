module sky130_fd_sc_hdll__a21boi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // Y matches the implemented NOR of ~B1_N and A1&A2.
    check_function_exact: assert property (
        @($global_clock) Y == ~(~B1_N | (A1 & A2))
    );

    // A low B1_N forces the output low.
    check_b1n_low_forces_y_low: assert property (
        @($global_clock) !B1_N |-> (Y == 1'b0)
    );

    // High A1 and A2 force the output low.
    check_a1_a2_high_force_y_low: assert property (
        @($global_clock) (A1 && A2) |-> (Y == 1'b0)
    );

    // B1_N high with A1&A2 not both high forces the output high.
    check_b1n_high_without_full_and_forces_y_high: assert property (
        @($global_clock) (B1_N && !(A1 && A2)) |-> (Y == 1'b1)
    );

    // A high output requires B1_N to be high.
    check_y_high_requires_b1n_high: assert property (
        @($global_clock) Y |-> B1_N
    );

    // A high output requires A1 and A2 not both high.
    check_y_high_requires_not_both_a_high: assert property (
        @($global_clock) Y |-> !(A1 && A2)
    );

    // With B1_N high, a low output means both A inputs are high.
    check_b1n_high_y_low_requires_a1_a2_high: assert property (
        @($global_clock) (B1_N && !Y) |-> (A1 && A2)
    );

endmodule