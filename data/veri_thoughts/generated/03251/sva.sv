module four_input_module_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic X
);

    // X matches the exact RTL expression.
    check_x_matches_rtl_expression: assert property (
        @($global_clock) X === ((A1 & A2 & A3) ? 1'b1 : (B1 ? 1'b0 : 1'b0))
    );

    // X is functionally the AND of A1, A2, and A3.
    check_x_equals_three_input_and: assert property (
        @($global_clock) X === (A1 & A2 & A3)
    );

    // All three A inputs high force X high.
    check_all_a_high_drives_x_high: assert property (
        @($global_clock) ((A1 & A2 & A3) === 1'b1) |-> (X === 1'b1)
    );

    // Any low A input forces X low.
    check_any_a_low_drives_x_low: assert property (
        @($global_clock) ((A1 === 1'b0) || (A2 === 1'b0) || (A3 === 1'b0)) |-> (X === 1'b0)
    );

    // X can only be high when all three A inputs are high.
    check_x_high_requires_all_a_high: assert property (
        @($global_clock) (X === 1'b1) |-> ((A1 & A2 & A3) === 1'b1)
    );

endmodule