module calculator_sva (
    input logic clk,
    input logic [3:0] reg_a,
    input logic [3:0] reg_b,
    input logic [1:0] op,
    input logic start,
    input logic [3:0] result
);

    // clk is an external sampling clock because the RTL has no native clock or reset.

    // op=00 returns the truncated sum.
    check_add_result: assert property (
        @(posedge clk)
        (op == 2'b00) |-> (result == ((reg_a + reg_b) & 4'hf))
    );

    // op=01 returns the truncated difference.
    check_subtract_result: assert property (
        @(posedge clk)
        (op == 2'b01) |-> (result == ((reg_a - reg_b) & 4'hf))
    );

    // op=10 returns the low 4 bits of the product.
    check_multiply_result: assert property (
        @(posedge clk)
        (op == 2'b10) |-> (result == ((reg_a * reg_b) & 4'hf))
    );

    // op=11 returns the quotient when the divisor is nonzero.
    check_divide_result: assert property (
        @(posedge clk)
        (op == 2'b11 && reg_b != 4'b0000) |-> (result == ((reg_a / reg_b) & 4'hf))
    );

    // With op and operands unchanged, the sampled result stays unchanged.
    check_result_stable_when_function_inputs_stable: assert property (
        @(posedge clk)
        ($stable(op) && $stable(reg_a) && $stable(reg_b) &&
         !((op == 2'b11) && (reg_b == 4'b0000))) |-> $stable(result)
    );

    // Changing start alone does not change the sampled result.
    check_start_does_not_change_result: assert property (
        @(posedge clk)
        ($changed(start) && $stable(op) && $stable(reg_a) && $stable(reg_b) &&
         !((op == 2'b11) && (reg_b == 4'b0000))) |-> $stable(result)
    );

endmodule