module and4b_sva (
    input logic A_N,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);

    // X must equal the implemented 4-input NOR function.
    check_x_matches_nor: assert property (
        @($global_clock) X == ~(A_N | B | C | D)
    );

    // X high means all four inputs are low.
    check_x_high_requires_all_inputs_low: assert property (
        @($global_clock) X |-> (!A_N && !B && !C && !D)
    );

    // All four inputs low must drive X high.
    check_all_inputs_low_drive_x_high: assert property (
        @($global_clock) (!A_N && !B && !C && !D) |-> X
    );

    // Any high input must drive X low.
    check_any_high_input_drives_x_low: assert property (
        @($global_clock) (A_N || B || C || D) |-> !X
    );

endmodule