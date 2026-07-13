module calculator_sva (
    input logic [7:0]  A,
    input logic [7:0]  B,
    input logic [1:0]  op,
    input logic [15:0] result
);

    // Addition mode drives the 16-bit sum.
    check_addition_mode: assert property (
        @($global_clock) (op == 2'b00) |-> (result == {8'h00, (A + B)})
    );

    // Subtraction mode drives the 16-bit difference.
    check_subtraction_mode: assert property (
        @($global_clock) (op == 2'b01) |-> (result == {8'h00, (A - B)})
    );

    // Multiplication mode drives the 16-bit product.
    check_multiplication_mode: assert property (
        @($global_clock) (op == 2'b10) |-> (result == {8'h00, (A * B)})
    );

    // Division mode drives the 16-bit quotient when the divisor is nonzero.
    check_division_mode: assert property (
        @($global_clock) ((op == 2'b11) && (B != 8'h00)) |-> (result == {8'h00, (A / B)})
    );

endmodule