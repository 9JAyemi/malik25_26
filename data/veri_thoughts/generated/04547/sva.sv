module and2_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B
);

    // Binary inputs produce the Boolean AND result.
    check_binary_inputs_match_and: assert property (
        @(posedge clk)
        (((A === 1'b0) || (A === 1'b1)) &&
         ((B === 1'b0) || (B === 1'b1)))
        |-> (X === (A & B))
    );

    // Any low input forces the output low.
    check_any_low_forces_output_low: assert property (
        @(posedge clk)
        ((A === 1'b0) || (B === 1'b0))
        |-> (X === 1'b0)
    );

    // Both high inputs drive the output high.
    check_both_high_drive_output_high: assert property (
        @(posedge clk)
        (A === 1'b1 && B === 1'b1)
        |-> (X === 1'b1)
    );

    // A high output requires both inputs high.
    check_output_high_requires_both_high: assert property (
        @(posedge clk)
        (X === 1'b1)
        |-> (A === 1'b1 && B === 1'b1)
    );

    // A low output implies at least one input is low.
    check_output_low_requires_any_low: assert property (
        @(posedge clk)
        (X === 1'b0)
        |-> ((A === 1'b0) || (B === 1'b0))
    );

    // The AND and buffer chain never drives high impedance.
    check_output_never_high_impedance: assert property (
        @(posedge clk)
        (X !== 1'bz)
    );

endmodule