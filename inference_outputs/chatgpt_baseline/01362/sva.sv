module calculator_sva (
    input logic CLK,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] op,
    input logic [15:0] result
);

    // When op==00, result equals 8-bit addition zero-extended.
    check_addition_result: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b00) |-> (result == (A + B))
    );

    // When op==01, result equals 8-bit subtraction zero-extended.
    check_subtraction_result: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b01) |-> (result == (A - B))
    );

    // When op==10, result equals 16-bit multiplication.
    check_multiplication_result: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b10) |-> (result == (A * B))
    );

    // When op==11 and B!=0, result equals 8-bit division zero-extended.
    check_division_result_no_div0: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b11 && (B != 8'd0)) |-> (result == (A / B))
    );

    // For addition, upper 8 bits are zero.
    check_upper_zero_for_add: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b00) |-> (result[15:8] == 8'h00)
    );

    // For subtraction, upper 8 bits are zero.
    check_upper_zero_for_sub: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b01) |-> (result[15:8] == 8'h00)
    );

    // For division with nonzero divisor, upper 8 bits are zero.
    check_upper_zero_for_div_no_div0: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b11 && (B != 8'd0)) |-> (result[15:8] == 8'h00)
    );

    // For multiplication, if either operand is zero, result is zero.
    check_mul_zero_operand_gives_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b10) && ((A == 8'd0) || (B == 8'd0)) |-> (result == 16'd0)
    );

    // For division with nonzero divisor, quotient is <= numerator.
    check_div_quotient_le_numerator: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b11 && (B != 8'd0)) |-> (result <= {8'd0, A})
    );

    // If inputs are stable across a cycle, result is stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (1'b0) $stable(A) && $stable(B) && $stable(op) |-> $stable(result)
    );

endmodule