module sky130_fd_sc_ls__a22o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // The A input pair drives X high when both A1 and A2 are high.
    check_a_pair_sets_x: assert property (
        @($global_clock) (A1 & A2) |-> X
    );

    // The B input pair drives X high when both B1 and B2 are high.
    check_b_pair_sets_x: assert property (
        @($global_clock) (B1 & B2) |-> X
    );

    // X is low when neither AND term is active.
    check_no_active_term_sets_x_low: assert property (
        @($global_clock) (~(A1 & A2) & ~(B1 & B2)) |-> ~X
    );

    // A high X must come from at least one active AND term.
    check_x_requires_active_term: assert property (
        @($global_clock) X |-> ((A1 & A2) | (B1 & B2))
    );

    // X matches the implemented AO22 boolean function.
    check_a22o_function: assert property (
        @($global_clock) X == ((A1 & A2) | (B1 & B2))
    );

endmodule