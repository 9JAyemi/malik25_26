module four_in_one_out_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // X must match the implemented combinational equation.
    check_output_definition: assert property (
        @($global_clock)
        X === (((A1 & A2) | (A3 & B1)) ? 1'b1 : 1'b0)
    );

    // A1 and A2 high must drive X high.
    check_a1_a2_path: assert property (
        @($global_clock)
        ((A1 & A2) === 1'b1) |-> (X === 1'b1)
    );

    // A3 and B1 high must drive X high.
    check_a3_b1_path: assert property (
        @($global_clock)
        ((A3 & B1) === 1'b1) |-> (X === 1'b1)
    );

    // If both product terms are low, X must be low.
    check_no_terms_low: assert property (
        @($global_clock)
        (((A1 & A2) === 1'b0) && ((A3 & B1) === 1'b0)) |-> (X === 1'b0)
    );

    // A high X must be caused by one of the two implemented terms.
    check_high_output_has_source: assert property (
        @($global_clock)
        (X === 1'b1) |-> (((A1 & A2) === 1'b1) || ((A3 & B1) === 1'b1))
    );

    // A low X means neither implemented term is high.
    check_low_output_has_no_source: assert property (
        @($global_clock)
        (X === 1'b0) |-> (((A1 & A2) === 1'b0) && ((A3 & B1) === 1'b0))
    );

endmodule