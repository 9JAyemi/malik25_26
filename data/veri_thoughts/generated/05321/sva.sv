module binary_or_sva(
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [2:0] out
);

    // Output must match the RTL De Morgan expression.
    check_out_matches_rtl_expression: assert property (
        @($global_clock) out == ~((~a) & (~b))
    );

    // Output must equal the bitwise OR of the inputs.
    check_out_matches_bitwise_or: assert property (
        @($global_clock) out == (a | b)
    );

    // With b at zero, the output must pass through a.
    check_a_passthrough_when_b_zero: assert property (
        @($global_clock) (b == 3'b000) |-> (out == a)
    );

    // With a at zero, the output must pass through b.
    check_b_passthrough_when_a_zero: assert property (
        @($global_clock) (a == 3'b000) |-> (out == b)
    );

    // With both inputs at zero, the output must be zero.
    check_zero_output_when_inputs_zero: assert property (
        @($global_clock) ((a == 3'b000) && (b == 3'b000)) |-> (out == 3'b000)
    );

endmodule