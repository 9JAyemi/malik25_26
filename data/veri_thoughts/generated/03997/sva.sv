module sky130_fd_sc_hdll__o31ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // Y matches the implemented O31AI logic function.
    check_o31ai_function: assert property (
        @($global_clock) Y == ~(B1 & (A1 | A2 | A3))
    );

    // B1 low forces the NAND-based output high.
    check_b1_low_forces_y_high: assert property (
        @($global_clock) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // With all A inputs low, the output must be high.
    check_all_a_low_forces_y_high: assert property (
        @($global_clock) ((A1 | A2 | A3) == 1'b0) |-> (Y == 1'b1)
    );

    // B1 high with any asserted A input forces the output low.
    check_active_inputs_force_y_low: assert property (
        @($global_clock) ((B1 == 1'b1) && ((A1 | A2 | A3) == 1'b1)) |-> (Y == 1'b0)
    );

    // A low output requires B1 high and at least one A input high.
    check_y_low_only_when_inputs_active: assert property (
        @($global_clock) (Y == 1'b0) |-> ((B1 == 1'b1) && ((A1 | A2 | A3) == 1'b1))
    );

    // A high output means B1 is low or all A inputs are low.
    check_y_high_matches_nand_condition: assert property (
        @($global_clock) (Y == 1'b1) |-> ((B1 == 1'b0) || ((A1 | A2 | A3) == 1'b0))
    );

endmodule