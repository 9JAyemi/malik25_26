module and4_nor_assertions (
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Y must equal the AND of all four inputs.
    check_and_function: assert property (
        @($global_clock) Y == (A & B & C & D)
    );

    // All inputs high must drive Y high.
    check_all_high_drives_y_high: assert property (
        @($global_clock) (A & B & C & D) |-> Y
    );

    // A low must force Y low.
    check_a_low_forces_y_low: assert property (
        @($global_clock) !A |-> !Y
    );

    // B low must force Y low.
    check_b_low_forces_y_low: assert property (
        @($global_clock) !B |-> !Y
    );

    // C low must force Y low.
    check_c_low_forces_y_low: assert property (
        @($global_clock) !C |-> !Y
    );

    // D low must force Y low.
    check_d_low_forces_y_low: assert property (
        @($global_clock) !D |-> !Y
    );

    // Y high requires A high.
    check_y_high_requires_a_high: assert property (
        @($global_clock) Y |-> A
    );

    // Y high requires B high.
    check_y_high_requires_b_high: assert property (
        @($global_clock) Y |-> B
    );

    // Y high requires C high.
    check_y_high_requires_c_high: assert property (
        @($global_clock) Y |-> C
    );

    // Y high requires D high.
    check_y_high_requires_d_high: assert property (
        @($global_clock) Y |-> D
    );

endmodule