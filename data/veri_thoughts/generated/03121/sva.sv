module calculator_sva (
    input logic       clk,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [1:0] op,
    input logic [7:0] out
);

    // RTL is combinational with no reset; clk is a sampling clock.

    // Addition mode drives the 8-bit sum.
    check_addition_mode: assert property (
        @(posedge clk)
        (op == 2'b00) |-> (out == ((in1 + in2) & 8'hFF))
    );

    // Subtraction mode drives the 8-bit difference.
    check_subtraction_mode: assert property (
        @(posedge clk)
        (op == 2'b01) |-> (out == ((in1 - in2) & 8'hFF))
    );

    // Multiplication mode drives the low 8 bits of the product.
    check_multiplication_mode: assert property (
        @(posedge clk)
        (op == 2'b10) |-> (out == ((in1 * in2) & 8'hFF))
    );

    // Division mode drives the quotient when the divisor is nonzero.
    check_division_mode: assert property (
        @(posedge clk)
        (op == 2'b11 && in2 != 8'h00) |-> (out == ((in1 / in2) & 8'hFF))
    );

endmodule