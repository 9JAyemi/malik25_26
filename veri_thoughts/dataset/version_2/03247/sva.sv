module JAND4B_assertions (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic O
);

    // Output equals the implemented NAND-chain function.
    check_output_function: assert property (
        @($global_clock) (O === ((A1 & A2 & A3) | ~A4))
    );

    // A low A4 forces the output high.
    check_a4_low_forces_output_high: assert property (
        @($global_clock) (A4 === 1'b0) |-> (O === 1'b1)
    );

    // High A1, A2, and A3 force the output high.
    check_a123_high_forces_output_high: assert property (
        @($global_clock) ((A1 === 1'b1) && (A2 === 1'b1) && (A3 === 1'b1)) |-> (O === 1'b1)
    );

    // With A4 high, a low A1 forces the output low.
    check_a4_high_a1_low_forces_output_low: assert property (
        @($global_clock) ((A4 === 1'b1) && (A1 === 1'b0)) |-> (O === 1'b0)
    );

    // With A4 high, a low A2 forces the output low.
    check_a4_high_a2_low_forces_output_low: assert property (
        @($global_clock) ((A4 === 1'b1) && (A2 === 1'b0)) |-> (O === 1'b0)
    );

    // With A4 high, a low A3 forces the output low.
    check_a4_high_a3_low_forces_output_low: assert property (
        @($global_clock) ((A4 === 1'b1) && (A3 === 1'b0)) |-> (O === 1'b0)
    );

    // A low output requires A4 to be high.
    check_output_low_requires_a4_high: assert property (
        @($global_clock) (O === 1'b0) |-> (A4 === 1'b1)
    );

    // A high output with A4 high requires A1, A2, and A3 high.
    check_output_high_with_a4_high_requires_a123_high: assert property (
        @($global_clock) ((O === 1'b1) && (A4 === 1'b1)) |-> ((A1 === 1'b1) && (A2 === 1'b1) && (A3 === 1'b1))
    );

endmodule