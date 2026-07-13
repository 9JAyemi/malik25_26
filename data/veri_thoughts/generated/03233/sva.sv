module calculator_sva (
    input logic [7:0] num1,
    input logic [7:0] num2,
    input logic [1:0] op_sel,
    input logic [15:0] result,
    input logic clk
);

    // op_sel 00 selects zero-extended 8-bit addition.
    check_addition_result: assert property (
        @(posedge clk)
        (op_sel == 2'b00) |-> ((result[7:0] == (num1 + num2)) && (result[15:8] == 8'h00))
    );

    // op_sel 01 selects zero-extended 8-bit subtraction.
    check_subtraction_result: assert property (
        @(posedge clk)
        (op_sel == 2'b01) |-> ((result[7:0] == (num1 - num2)) && (result[15:8] == 8'h00))
    );

    // op_sel 10 selects the full 16-bit product.
    check_multiplication_result: assert property (
        @(posedge clk)
        (op_sel == 2'b10) |-> (result == ({8'h00, num1} * {8'h00, num2}))
    );

    // op_sel 11 with a nonzero divisor selects zero-extended division.
    check_division_result: assert property (
        @(posedge clk)
        ((op_sel == 2'b11) && (num2 != 8'h00)) |-> ((result[7:0] == (num1 / num2)) && (result[15:8] == 8'h00))
    );

    // Stable sampled inputs keep the sampled result stable.
    check_stable_inputs_hold_result: assert property (
        @(posedge clk)
        ($stable({num1, num2, op_sel}) && !((op_sel == 2'b11) && (num2 == 8'h00))) |-> $stable(result)
    );

endmodule