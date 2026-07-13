module nand_gate_sva (
    input logic A,
    input logic B,
    input logic X,
    input logic SLEEP_B
);

    // X must always match the implemented NAND-with-sleep function.
    check_x_matches_function: assert property (
        @($global_clock) X == (~(A & B) & SLEEP_B)
    );

    // Sleep low forces X low.
    check_sleep_forces_low: assert property (
        @($global_clock) !SLEEP_B |-> !X
    );

    // With sleep high and both inputs high, X is low.
    check_nand_high_high: assert property (
        @($global_clock) (SLEEP_B && A && B) |-> !X
    );

    // With sleep high and A low, X is high.
    check_nand_a_low: assert property (
        @($global_clock) (SLEEP_B && !A) |-> X
    );

    // With sleep high and B low, X is high.
    check_nand_b_low: assert property (
        @($global_clock) (SLEEP_B && !B) |-> X
    );

endmodule