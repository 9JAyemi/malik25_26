module calculator_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] op,
    input logic [15:0] result
);

    // Addition mode returns the 16-bit sum.
    check_add_result: assert property (
        @($global_clock) (op == 2'b00) |-> (result == ({8'b0, A} + {8'b0, B}))
    );

    // Subtraction mode returns the 16-bit difference.
    check_sub_result: assert property (
        @($global_clock) (op == 2'b01) |-> (result == ({8'b0, A} - {8'b0, B}))
    );

    // Multiplication mode returns the 16-bit product.
    check_mul_result: assert property (
        @($global_clock) (op == 2'b10) |-> (result == ({8'b0, A} * {8'b0, B}))
    );

    // Division mode returns the 16-bit quotient when the divisor is nonzero.
    check_div_result: assert property (
        @($global_clock) ((op == 2'b11) && (B != 8'h00)) |-> (result == ({8'b0, A} / {8'b0, B}))
    );

    // Stable inputs must keep the output stable.
    check_stable_inputs_stable_result: assert property (
        @($global_clock) $stable({A, B, op}) |-> $stable(result)
    );

endmodule