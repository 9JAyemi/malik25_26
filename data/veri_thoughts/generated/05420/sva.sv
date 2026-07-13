module calculator_sva (
    input logic clk,
    input logic signed [3:0] op1,
    input logic signed [3:0] op2,
    input logic [1:0] op,
    input logic signed [3:0] result
);

    function automatic logic signed [3:0] calc_expected (
        input logic signed [3:0] f_op1,
        input logic signed [3:0] f_op2,
        input logic [1:0] f_op
    );
    begin
        calc_expected = 4'bxxxx;
        case (f_op)
            2'b00: calc_expected = f_op1 + f_op2;
            2'b01: calc_expected = f_op1 - f_op2;
            2'b10: calc_expected = f_op1 * f_op2;
            2'b11: begin
                if (f_op2 == 0)
                    calc_expected = 4'bxxxx;
                else if ((f_op1 == -8) && (f_op2 == -1))
                    calc_expected = 4'bxxxx;
                else
                    calc_expected = f_op1 / f_op2;
            end
            default: calc_expected = 4'bxxxx;
        endcase
    end
    endfunction

    // Addition mode returns the 4-bit signed sum.
    check_addition_result: assert property (
        @(posedge clk) (op == 2'b00) |-> (result === calc_expected(op1, op2, op))
    );

    // Subtraction mode returns the 4-bit signed difference.
    check_subtraction_result: assert property (
        @(posedge clk) (op == 2'b01) |-> (result === calc_expected(op1, op2, op))
    );

    // Multiplication mode returns the truncated 4-bit signed product.
    check_multiplication_result: assert property (
        @(posedge clk) (op == 2'b10) |-> (result === calc_expected(op1, op2, op))
    );

    // Division mode returns the signed quotient for non-exception cases.
    check_division_result: assert property (
        @(posedge clk)
        (op == 2'b11 && (op2 != 0) && !((op1 == -8) && (op2 == -1)))
        |-> (result === calc_expected(op1, op2, op))
    );

endmodule