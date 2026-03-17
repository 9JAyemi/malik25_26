module four_input_gate_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // X matches the implemented gate equation.
    check_gate_equation: assert property (
        @($global_clock)
        X == (((A1 & A2) | (B1 & B2)) & !(A1 & A2 & B1 & B2))
    );

    // Only the A input pair being high drives X high.
    check_a_pair_only_sets_x: assert property (
        @($global_clock)
        (((A1 & A2) == 1'b1) && ((B1 & B2) == 1'b0)) |-> (X == 1'b1)
    );

    // Only the B input pair being high drives X high.
    check_b_pair_only_sets_x: assert property (
        @($global_clock)
        (((A1 & A2) == 1'b0) && ((B1 & B2) == 1'b1)) |-> (X == 1'b1)
    );

    // Both input pairs high force X low.
    check_both_pairs_clear_x: assert property (
        @($global_clock)
        ((A1 == 1'b1) && (A2 == 1'b1) && (B1 == 1'b1) && (B2 == 1'b1)) |-> (X == 1'b0)
    );

    // With no complete input pair, X stays low.
    check_no_complete_pair_clear_x: assert property (
        @($global_clock)
        (((A1 & A2) == 1'b0) && ((B1 & B2) == 1'b0)) |-> (X == 1'b0)
    );

    // A high X means exactly one input pair is complete.
    check_x_implies_one_complete_pair: assert property (
        @($global_clock)
        (X == 1'b1) |-> (((A1 & A2) ^ (B1 & B2)) == 1'b1)
    );

endmodule