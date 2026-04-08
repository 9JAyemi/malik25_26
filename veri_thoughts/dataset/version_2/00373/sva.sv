module sky130_fd_sc_ms__o2bb2a_sva (
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

    // X must match the implemented NAND-OR-AND function.
    check_function_exact: assert property (
        @($global_clock)
        X == ((~(A2_N & A1_N)) & (B2 | B1))
    );

    // Both A inputs high force the NAND leg low, so X must be low.
    check_a_inputs_both_high_force_low: assert property (
        @($global_clock)
        ((A1_N == 1'b1) && (A2_N == 1'b1)) |-> (X == 1'b0)
    );

    // Both B inputs low force the OR leg low, so X must be low.
    check_b_inputs_both_low_force_low: assert property (
        @($global_clock)
        ((B1 == 1'b0) && (B2 == 1'b0)) |-> (X == 1'b0)
    );

    // A low A1_N with either B input high must drive X high.
    check_a1_low_with_b_high_sets_x: assert property (
        @($global_clock)
        ((A1_N == 1'b0) && ((B1 == 1'b1) || (B2 == 1'b1))) |-> (X == 1'b1)
    );

    // A low A2_N with either B input high must drive X high.
    check_a2_low_with_b_high_sets_x: assert property (
        @($global_clock)
        ((A2_N == 1'b0) && ((B1 == 1'b1) || (B2 == 1'b1))) |-> (X == 1'b1)
    );

    // A high X requires at least one B input to be high.
    check_x_high_requires_b_or: assert property (
        @($global_clock)
        (X == 1'b1) |-> ((B1 == 1'b1) || (B2 == 1'b1))
    );

    // A high X requires at least one A input to be low.
    check_x_high_requires_a_nand_true: assert property (
        @($global_clock)
        (X == 1'b1) |-> ((A1_N == 1'b0) || (A2_N == 1'b0))
    );

endmodule