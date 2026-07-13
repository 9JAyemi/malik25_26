module sky130_fd_sc_hvl__a22o_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X
);

    // No explicit clock or reset in RTL; sample on the formal global clock.

    // X must match the RTL boolean function.
    check_x_matches_rtl_function: assert property (
        @($global_clock)
        X == ((A1 & A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2))
    );

    // A=11 and B=00 must drive X high.
    check_x_high_for_a11_b00: assert property (
        @($global_clock)
        (A1 & A2 & ~B1 & ~B2) |-> X
    );

    // A=00 and B=11 must drive X high.
    check_x_high_for_a00_b11: assert property (
        @($global_clock)
        (~A1 & ~A2 & B1 & B2) |-> X
    );

    // X high can only come from one of the two implemented minterms.
    check_x_high_only_for_implemented_minterms: assert property (
        @($global_clock)
        X |-> ((A1 & A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2))
    );

    // Any mismatch on the A inputs must force X low.
    check_x_low_when_a_inputs_differ: assert property (
        @($global_clock)
        (A1 ^ A2) |-> !X
    );

    // Any mismatch on the B inputs must force X low.
    check_x_low_when_b_inputs_differ: assert property (
        @($global_clock)
        (B1 ^ B2) |-> !X
    );

    // All four equal inputs must drive X low.
    check_x_low_when_all_inputs_equal: assert property (
        @($global_clock)
        ((~A1 & ~A2 & ~B1 & ~B2) | (A1 & A2 & B1 & B2)) |-> !X
    );

endmodule