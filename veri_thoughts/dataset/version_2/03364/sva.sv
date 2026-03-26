module bit_shift_sva (
    input logic clk,
    input logic [31:0] in,
    input logic [4:0] shift_amount,
    input logic [1:0] shift_type,
    input logic [31:0] out
);

    // Left-shift mode matches in shifted left by shift_amount.
    check_logical_left_shift: assert property (
        @(posedge clk)
        (shift_type == 2'b00) |-> (out == (in << shift_amount))
    );

    // Right-shift mode matches in shifted right by shift_amount.
    check_logical_right_shift: assert property (
        @(posedge clk)
        (shift_type == 2'b01) |-> (out == (in >> shift_amount))
    );

    // Arithmetic right-shift mode matches signed in shifted right by shift_amount.
    check_arithmetic_right_shift: assert property (
        @(posedge clk)
        (shift_type == 2'b10) |-> (out == ($signed(in) >>> shift_amount))
    );

    // Default mode passes the input through unchanged.
    check_default_passthrough: assert property (
        @(posedge clk)
        (shift_type == 2'b11) |-> (out == in)
    );

    // A zero shift amount leaves the output equal to the input.
    check_zero_shift_passthrough: assert property (
        @(posedge clk)
        (shift_amount == 5'd0) |-> (out == in)
    );

    // Arithmetic right shift preserves a 1 sign bit for negative inputs.
    check_arith_shift_negative_sign_fill: assert property (
        @(posedge clk)
        (shift_type == 2'b10 && shift_amount != 5'd0 && in[31] == 1'b1) |-> (out[31] == 1'b1)
    );

    // Arithmetic right shift preserves a 0 sign bit for non-negative inputs.
    check_arith_shift_positive_sign_fill: assert property (
        @(posedge clk)
        (shift_type == 2'b10 && shift_amount != 5'd0 && in[31] == 1'b0) |-> (out[31] == 1'b0)
    );

endmodule