module and4bb_sva (
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D,
    input logic X
);

    // X must equal the AND of all four inputs.
    check_x_matches_and: assert property (
        @($global_clock) X == (A_N & B_N & C & D)
    );

    // All inputs high must drive X high.
    check_all_inputs_high_drive_x_high: assert property (
        @($global_clock) (A_N && B_N && C && D) |-> X
    );

    // A_N low must force X low.
    check_a_n_low_forces_x_low: assert property (
        @($global_clock) !A_N |-> !X
    );

    // B_N low must force X low.
    check_b_n_low_forces_x_low: assert property (
        @($global_clock) !B_N |-> !X
    );

    // C low must force X low.
    check_c_low_forces_x_low: assert property (
        @($global_clock) !C |-> !X
    );

    // D low must force X low.
    check_d_low_forces_x_low: assert property (
        @($global_clock) !D |-> !X
    );

endmodule