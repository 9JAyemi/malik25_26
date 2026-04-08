module calculator_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result,
    input logic valid
);

    // Addition returns the 8-bit sum and sets valid.
    check_add_result: assert property (
        @(posedge clk)
        (op == 2'b00) |-> ((result == (a + b)) && (valid == 1'b1))
    );

    // Subtraction returns the 8-bit difference and sets valid.
    check_sub_result: assert property (
        @(posedge clk)
        (op == 2'b01) |-> ((result == (a - b)) && (valid == 1'b1))
    );

    // Multiplication returns the low 8 bits of the product and sets valid.
    check_mul_result: assert property (
        @(posedge clk)
        (op == 2'b10) |-> ((result == ((a * b) & 16'h00FF)) && (valid == 1'b1))
    );

    // Division by zero forces a zero result and clears valid.
    check_div_zero_result: assert property (
        @(posedge clk)
        ((op == 2'b11) && (b == 8'h00)) |-> ((result == 8'h00) && (valid == 1'b0))
    );

    // Division by a nonzero operand returns the quotient and sets valid.
    check_div_nonzero_result: assert property (
        @(posedge clk)
        ((op == 2'b11) && (b != 8'h00)) |-> ((result == (a / b)) && (valid == 1'b1))
    );

    // valid can be low only for division by zero.
    check_valid_low_only_on_div_zero: assert property (
        @(posedge clk)
        (valid == 1'b0) |-> ((op == 2'b11) && (b == 8'h00))
    );

    // Any case other than division by zero must set valid.
    check_valid_high_otherwise: assert property (
        @(posedge clk)
        (!((op == 2'b11) && (b == 8'h00))) |-> (valid == 1'b1)
    );

    // valid depends only on op and b, not on a.
    check_valid_stable_when_op_b_stable: assert property (
        @(posedge clk)
        ($stable(op) && $stable(b)) |-> $stable(valid)
    );

endmodule