module calculator_sva (
    input logic signed [15:0] a,
    input logic signed [15:0] b,
    input logic [1:0] op,
    input logic signed [15:0] result
);
    typedef logic signed [15:0] s16_t;

    // Addition opcode drives the 16-bit signed sum.
    check_add_result: assert property (
        @($global_clock) (op == 2'b00) |-> (result == s16_t'(a + b))
    );

    // Subtraction opcode drives the 16-bit signed difference.
    check_sub_result: assert property (
        @($global_clock) (op == 2'b01) |-> (result == s16_t'(a - b))
    );

    // Multiplication opcode drives the truncated 16-bit signed product.
    check_mul_result: assert property (
        @($global_clock) (op == 2'b10) |-> (result == s16_t'(a * b))
    );

    // Division opcode drives the 16-bit signed quotient when the divisor is nonzero.
    check_div_result: assert property (
        @($global_clock) ((op == 2'b11) && (b != 16'sd0)) |-> (result == s16_t'(a / b))
    );

endmodule