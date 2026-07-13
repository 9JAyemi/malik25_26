module sky130_fd_sc_hdll__nand3b_sva (
    input logic Y,
    input logic A_N,
    input logic B,
    input logic C
);

    // Y matches the implemented NAND-with-inverted-A function.
    check_functional_equivalence: assert property (
        @($global_clock) (Y == ~(B & ~A_N & C))
    );

    // A_N high forces Y high.
    check_a_n_high_forces_y_high: assert property (
        @($global_clock) A_N |-> Y
    );

    // B low forces Y high.
    check_b_low_forces_y_high: assert property (
        @($global_clock) (!B) |-> Y
    );

    // C low forces Y high.
    check_c_low_forces_y_high: assert property (
        @($global_clock) (!C) |-> Y
    );

    // With B and C high, Y reduces to A_N.
    check_b_c_high_reduces_to_a_n: assert property (
        @($global_clock) (B && C) |-> (Y == A_N)
    );

    // With A_N low and C high, Y reduces to inverted B.
    check_a_n_low_c_high_reduces_to_not_b: assert property (
        @($global_clock) ((!A_N) && C) |-> (Y == ~B)
    );

    // With A_N low and B high, Y reduces to inverted C.
    check_a_n_low_b_high_reduces_to_not_c: assert property (
        @($global_clock) ((!A_N) && B) |-> (Y == ~C)
    );

    // Y low requires A_N low with B and C high.
    check_y_low_requires_specific_inputs: assert property (
        @($global_clock) (!Y) |-> ((!A_N) && B && C)
    );

endmodule