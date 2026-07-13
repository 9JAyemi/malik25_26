module logical_and3b_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

    // X must always equal the three-input AND of A, B, and C.
    check_x_matches_and3: assert property (
        @($global_clock) X == (A & B & C)
    );

    // X can be high only when all three inputs are high.
    check_x_high_requires_all_inputs_high: assert property (
        @($global_clock) X |-> (A & B & C)
    );

    // All three high inputs must drive X high.
    check_all_inputs_high_drive_x_high: assert property (
        @($global_clock) (A & B & C) |-> X
    );

    // A low must force X low.
    check_a_low_forces_x_low: assert property (
        @($global_clock) !A |-> !X
    );

    // B low must force X low.
    check_b_low_forces_x_low: assert property (
        @($global_clock) !B |-> !X
    );

    // C low must force X low.
    check_c_low_forces_x_low: assert property (
        @($global_clock) !C |-> !X
    );

endmodule