module calculator_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] op,
    input logic [7:0] result
);

    // Addition mode returns the low 8 bits of A + B.
    check_add_result: assert property (
        @(posedge clk)
        (op == 2'b00) |-> (result == ((A + B) & 8'hFF))
    );

    // Subtraction mode returns the low 8 bits of A - B.
    check_sub_result: assert property (
        @(posedge clk)
        (op == 2'b01) |-> (result == ((A - B) & 8'hFF))
    );

    // Multiplication mode returns the low 8 bits of A * B.
    check_mul_result: assert property (
        @(posedge clk)
        (op == 2'b10) |-> (result == ((A * B) & 8'hFF))
    );

    // Division mode returns A / B when the divisor is nonzero.
    check_div_result_nonzero: assert property (
        @(posedge clk)
        ((op == 2'b11) && (B != 8'h00)) |-> (result == (A / B))
    );

    // Stable inputs must keep the sampled result stable.
    check_result_stable_when_inputs_stable: assert property (
        @(posedge clk)
        $stable({A, B, op}) |-> $stable(result)
    );

    // Multiplication by zero must produce zero.
    check_mul_zero_operand: assert property (
        @(posedge clk)
        ((op == 2'b10) && ((A == 8'h00) || (B == 8'h00))) |-> (result == 8'h00)
    );

    // Division by one must pass A through unchanged.
    check_div_by_one_passthrough: assert property (
        @(posedge clk)
        ((op == 2'b11) && (B == 8'h01)) |-> (result == A)
    );

    // Unsigned division yields zero when A is smaller than nonzero B.
    check_div_smaller_numerator_zero: assert property (
        @(posedge clk)
        ((op == 2'b11) && (B != 8'h00) && (A < B)) |-> (result == 8'h00)
    );

endmodule