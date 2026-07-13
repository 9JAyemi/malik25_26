module calculator_sva (
    input logic        clk,
    input logic        reset_n,
    input logic [31:0] operand1,
    input logic [31:0] operand2,
    input logic [1:0]  operation,
    input logic [31:0] result
);

    // A clock sampled during reset forces result to zero by the next sample.
    check_reset_clears_result: assert property (
        @(posedge clk) !reset_n |=> (result == 32'd0)
    );

    // Addition updates result with operand1 + operand2.
    check_add_result: assert property (
        @(posedge clk) disable iff (!reset_n)
        (operation == 2'b00) |=> (result == (($past(operand1) + $past(operand2)) & 32'hFFFF_FFFF))
    );

    // Subtraction updates result with operand1 - operand2.
    check_sub_result: assert property (
        @(posedge clk) disable iff (!reset_n)
        (operation == 2'b01) |=> (result == (($past(operand1) - $past(operand2)) & 32'hFFFF_FFFF))
    );

    // Multiplication updates result with the low 32 bits of operand1 * operand2.
    check_mul_result: assert property (
        @(posedge clk) disable iff (!reset_n)
        (operation == 2'b10) |=> (result == (($past(operand1) * $past(operand2)) & 32'hFFFF_FFFF))
    );

    // Division updates result with operand1 / operand2 when the divisor is nonzero.
    check_div_result_nonzero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (operation == 2'b11 && operand2 != 32'd0) |=> (result == ($past(operand1) / $past(operand2)))
    );

endmodule