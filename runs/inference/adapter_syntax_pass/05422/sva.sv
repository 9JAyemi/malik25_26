module calculator_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] op,
    input logic [7:0] result
);

    // op 00 selects the 8-bit sum of A and B.
    check_add_result: assert property (
        @($global_clock) (op == 2'b00) |-> (result == ((A + B) & 8'hFF))
    );

    // op 01 selects the 8-bit difference of A and B.
    check_sub_result: assert property (
        @($global_clock) (op == 2'b01) |-> (result == ((A - B) & 8'hFF))
    );

    // op 10 selects the low 8 bits of the product of A and B.
    check_mul_result: assert property (
        @($global_clock) (op == 2'b10) |-> (result == ((A * B) & 8'hFF))
    );

    // op 11 with a nonzero divisor selects the quotient of A divided by B.
    check_div_nonzero_result: assert property (
        @($global_clock) ((op == 2'b11) && (B != 8'h00)) |-> (result == ((A / B) & 8'hFF))
    );

    // op 11 with a zero divisor forces the result to zero.
    check_div_zero_result: assert property (
        @($global_clock) ((op == 2'b11) && (B == 8'h00)) |-> (result == 8'h00)
    );

    // op values other than 00, 01, 10, or 11 force the result to zero.
    check_default_result: assert property (
        @($global_clock) ((op != 2'b00) && (op != 2'b01) && (op != 2'b10) && (op != 2'b11)) |-> (result == 8'h00)
    );

endmodule