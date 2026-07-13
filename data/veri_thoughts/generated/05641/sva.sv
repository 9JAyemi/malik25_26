module sky130_fd_sc_ms__o21ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    // Y matches the O21AI boolean function.
    check_o21ai_function: assert property (
        @($global_clock) Y == ~((A1 | A2) & B1)
    );

    // A low B1 forces the output high.
    check_b1_low_forces_y_high: assert property (
        @($global_clock) !B1 |-> Y
    );

    // Both OR inputs low force the output high.
    check_a1_a2_low_forces_y_high: assert property (
        @($global_clock) (!A1 && !A2) |-> Y
    );

    // B1 high with A1 high forces the output low.
    check_a1_b1_high_forces_y_low: assert property (
        @($global_clock) (B1 && A1) |-> !Y
    );

    // B1 high with A2 high forces the output low.
    check_a2_b1_high_forces_y_low: assert property (
        @($global_clock) (B1 && A2) |-> !Y
    );

    // A low output requires B1 high and at least one A input high.
    check_y_low_only_for_valid_condition: assert property (
        @($global_clock) !Y |-> (B1 && (A1 || A2))
    );

    // A high output requires B1 low or both A inputs low.
    check_y_high_only_for_valid_condition: assert property (
        @($global_clock) Y |-> (!B1 || (!A1 && !A2))
    );

endmodule