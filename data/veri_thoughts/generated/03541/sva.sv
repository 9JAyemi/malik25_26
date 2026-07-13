module calculator_sva (
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [1:0]  op,
    input logic [31:0] Z
);

    // op 00 drives the sum of A and B.
    check_add_result: assert property (
        @($global_clock) (op == 2'b00) |-> (Z == ((A + B) & 32'hFFFF_FFFF))
    );

    // op 01 drives the difference of A and B.
    check_sub_result: assert property (
        @($global_clock) (op == 2'b01) |-> (Z == ((A - B) & 32'hFFFF_FFFF))
    );

    // op 10 drives the lower 32 bits of the product of A and B.
    check_mul_result: assert property (
        @($global_clock) (op == 2'b10) |-> (Z == ((A * B) & 32'hFFFF_FFFF))
    );

    // op 11 drives the quotient when the divisor is nonzero.
    check_div_result_nonzero: assert property (
        @($global_clock) ((op == 2'b11) && (B != 32'h0000_0000)) |-> (Z == ((A / B) & 32'hFFFF_FFFF))
    );

    // With unchanged inputs, the combinational output stays unchanged.
    check_output_stable_when_inputs_stable: assert property (
        @($global_clock) $stable({A, B, op}) |-> $stable(Z)
    );

endmodule