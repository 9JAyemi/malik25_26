module or4_assertions (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // X must equal the OR of all four inputs.
    check_or_function: assert property (
        @($global_clock) X == (A | B | C | D)
    );

    // A high must drive X high.
    check_a_drives_x_high: assert property (
        @($global_clock) A |-> X
    );

    // B high must drive X high.
    check_b_drives_x_high: assert property (
        @($global_clock) B |-> X
    );

    // C high must drive X high.
    check_c_drives_x_high: assert property (
        @($global_clock) C |-> X
    );

    // D high must drive X high.
    check_d_drives_x_high: assert property (
        @($global_clock) D |-> X
    );

    // All inputs low must drive X low.
    check_all_low_drives_x_low: assert property (
        @($global_clock) (!A && !B && !C && !D) |-> !X
    );

    // X low implies no input is high.
    check_x_low_means_all_inputs_low: assert property (
        @($global_clock) !X |-> (!A && !B && !C && !D)
    );

endmodule