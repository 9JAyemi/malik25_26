module nor_and_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);

    // Y must match the implemented NOR-then-AND logic.
    check_output_matches_gate_function: assert property (
        @($global_clock) Y == ((~(A | B)) & C_N & D_N)
    );

    // A high forces the NOR term low, so Y must be low.
    check_a_high_forces_y_low: assert property (
        @($global_clock) A |-> !Y
    );

    // B high forces the NOR term low, so Y must be low.
    check_b_high_forces_y_low: assert property (
        @($global_clock) B |-> !Y
    );

    // C_N low clears the AND term, so Y must be low.
    check_c_n_low_forces_y_low: assert property (
        @($global_clock) !C_N |-> !Y
    );

    // D_N low clears the AND term, so Y must be low.
    check_d_n_low_forces_y_low: assert property (
        @($global_clock) !D_N |-> !Y
    );

    // When all enabling inputs are asserted, Y must be high.
    check_all_enabling_inputs_drive_y_high: assert property (
        @($global_clock) (!A && !B && C_N && D_N) |-> Y
    );

    // A high Y requires both NOR inputs low and both AND inputs high.
    check_y_high_requires_all_terms_true: assert property (
        @($global_clock) Y |-> (!A && !B && C_N && D_N)
    );

    // With A and B low, Y reduces to C_N AND D_N.
    check_ab_low_reduces_to_cd_and: assert property (
        @($global_clock) (!A && !B) |-> (Y == (C_N & D_N))
    );

    // With C_N and D_N high, Y reduces to NOR(A,B).
    check_cd_high_reduces_to_ab_nor: assert property (
        @($global_clock) (C_N && D_N) |-> (Y == (~(A | B)))
    );

endmodule