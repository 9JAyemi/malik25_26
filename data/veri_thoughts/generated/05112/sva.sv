module my_module_sva (
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic X
);

    // No explicit clock or reset in RTL; assertions use $global_clock.

    // If A1 is low, X must be low.
    check_a1_low_forces_x_low: assert property (
        @($global_clock) (!A1) |-> (X == 1'b0)
    );

    // If A1 and A2 are high, X must be high.
    check_a1_a2_high_force_x_high: assert property (
        @($global_clock) (A1 && A2) |-> (X == 1'b1)
    );

    // If A1 is high and A2 is low, X must be the inverse of B1_N.
    check_else_branch_uses_inverted_b1_n: assert property (
        @($global_clock) (A1 && !A2) |-> (X == ~B1_N)
    );

    // X must match the implemented combinational function.
    check_x_matches_implemented_function: assert property (
        @($global_clock) (X == (A1 & (A2 | ~B1_N)))
    );

endmodule