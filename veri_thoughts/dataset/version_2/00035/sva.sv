module math_op_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result
);

    typedef logic [7:0] byte_t;

    // Addition mode returns the 8-bit sum of a and b.
    check_add_result: assert property (
        @(posedge clk) (op == 2'b00) |-> (result == byte_t'(a + b))
    );

    // Subtraction mode returns the 8-bit difference of a and b.
    check_sub_result: assert property (
        @(posedge clk) (op == 2'b01) |-> (result == byte_t'(a - b))
    );

    // Multiplication mode returns the low 8 bits of the product.
    check_mul_result: assert property (
        @(posedge clk) (op == 2'b10) |-> (result == byte_t'(a * b))
    );

    // Division by zero forces the result to zero.
    check_div_by_zero_result: assert property (
        @(posedge clk) ((op == 2'b11) && (b == 8'd0)) |-> (result == 8'd0)
    );

    // Division mode returns the 8-bit quotient when b is nonzero.
    check_div_result: assert property (
        @(posedge clk) ((op == 2'b11) && (b != 8'd0)) |-> (result == byte_t'(a / b))
    );

endmodule