module sky130_fd_sc_lp__or2b_sva (
    input logic X,
    input logic A,
    input logic B_N
);

    // X implements A OR the inversion of B_N.
    check_or2b_boolean_function: assert property (
        @($global_clock) X == (A | ~B_N)
    );

    // A high forces X high.
    check_a_high_forces_x_high: assert property (
        @($global_clock) A |-> X
    );

    // B_N low forces X high through the inverted input.
    check_bn_low_forces_x_high: assert property (
        @($global_clock) !B_N |-> X
    );

    // X can be low only when A is low and B_N is high.
    check_x_low_unique_input_case: assert property (
        @($global_clock) !X |-> (!A && B_N)
    );

    // When B_N is high, X follows A.
    check_bn_high_makes_x_follow_a: assert property (
        @($global_clock) B_N |-> (X == A)
    );

endmodule