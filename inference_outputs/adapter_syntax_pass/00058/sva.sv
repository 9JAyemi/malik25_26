module calculator_sva (
    input logic [7:0] num1,
    input logic [7:0] num2,
    input logic [1:0] op,
    input logic [7:0] result
);

    // op=00 selects 8-bit addition.
    check_add_operation: assert property (
        @($global_clock) (op == 2'b00) |-> (result == ((num1 + num2) & 8'hFF))
    );

    // op=01 selects 8-bit subtraction.
    check_sub_operation: assert property (
        @($global_clock) (op == 2'b01) |-> (result == ((num1 - num2) & 8'hFF))
    );

    // op=10 selects 8-bit multiplication.
    check_mul_operation: assert property (
        @($global_clock) (op == 2'b10) |-> (result == ((num1 * num2) & 8'hFF))
    );

    // op=11 selects 8-bit division when the divisor is nonzero.
    check_div_operation: assert property (
        @($global_clock) ((op == 2'b11) && (num2 != 8'h00)) |-> (result == ((num1 / num2) & 8'hFF))
    );

endmodule