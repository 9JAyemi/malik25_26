module alu_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [4:0]  aluc,
    input logic [31:0] result
);

    // Addition (signed) returns the 32-bit sum.
    check_add_signed: assert property (
        @(posedge clk) (aluc == 5'd0) |-> (result == (a + b))
    );

    // Addition (unsigned) returns the 32-bit sum.
    check_add_unsigned: assert property (
        @(posedge clk) (aluc == 5'd1) |-> (result == (a + b))
    );

    // Subtraction (signed) returns the 32-bit difference.
    check_sub_signed: assert property (
        @(posedge clk) (aluc == 5'd2) |-> (result == (a - b))
    );

    // Subtraction (unsigned) returns the 32-bit difference.
    check_sub_unsigned: assert property (
        @(posedge clk) (aluc == 5'd3) |-> (result == (a - b))
    );

    // Bitwise AND returns the 32-bit AND of the inputs.
    check_and: assert property (
        @(posedge clk) (aluc == 5'd4) |-> (result == (a & b))
    );

    // Bitwise OR returns the 32-bit OR of the inputs.
    check_or: assert property (
        @(posedge clk) (aluc == 5'd5) |-> (result == (a | b))
    );

    // Bitwise XOR returns the 32-bit XOR of the inputs.
    check_xor: assert property (
        @(posedge clk) (aluc == 5'd6) |-> (result == (a ^ b))
    );

    // Bitwise NOR returns the 32-bit NOR of the inputs.
    check_nor: assert property (
        @(posedge clk) (aluc == 5'd7) |-> (result == ~(a | b))
    );

    // Set Less Than (signed) returns 1 when a is negative and b is non-negative.
    check_slt_signed_sign: assert property (
        @(posedge clk) ((aluc == 5'd8) && (a[31] == 1'b1) && (b[31] == 1'b0)) |-> (result == 32'd1)
    );

    // Set Less Than (signed) returns 1 when a is non-negative and b is negative.
    check_slt_signed_b_negative: assert property (
        @(posedge clk) ((aluc == 5'd8) && (a[31] == 1'b0) && (b[31] == 1'b1)) |-> (result == 32'd1)
    );

    // Set Less Than (signed) returns 1 when a is less than b.
    check_slt_signed_less_than: assert property (
        @(posedge clk) ((aluc == 5'd8) && (a[31] == 1'b0) && (b[31] == 1'b0) && (a < b)) |-> (result == 32'd1)
    );

    // Set Less Than (signed) returns 0 when a is greater than or equal to b.
    check_slt_signed_not_less_than: assert property (
        @(posedge clk) ((aluc == 5'd8) && (a[31] == 1'b0) && (b[31] == 1'b0) && (a >= b)) |-> (result == 32'd0)
    );

    // Set Less Than (unsigned) returns 1 when a is less than b.
    check_slt_unsigned_less_than: assert property (
        @(posedge clk) ((aluc == 5'd9) && (a < b)) |-> (result == 32'd1)
    );

    // Set Less Than (unsigned) returns 0 when a is greater than or equal to b.
    check_slt_unsigned_not_less_than: assert property (
        @(posedge clk) ((aluc == 5'd9) && (a >= b)) |-> (result == 32'd0)
    );

    // Shift Left Logical returns b shifted left by a.
    check_shift_left_logical: assert property (
        @(posedge clk) (aluc == 5'd10) |-> (result == (b << a))
    );

    // Shift Right Logical returns b shifted right by a.
    check_shift_right_logical: assert property (
        @(posedge clk) (aluc == 5'd11) |-> (result == (b >> a))
    );

    // Shift Right Arithmetic returns the arithmetic right shift of b by a.
    check_shift_right_arithmetic: assert property (
        @(posedge clk) (aluc == 5'd12) |-> (result == ($signed(b) >>> a))
    );

    // Load Upper Immediate returns the upper 16 bits of b with zero-extended low 16 bits.
    check_load_upper_immediate: assert property (
        @(posedge clk) (aluc == 5'd14) |-> (result == {b[15:0], 16'h0000})
    );

    // Zero returns zero.
    check_zero: assert property (
        @(posedge clk) (aluc == 5'd31) |-> (result == 32'd0)
    );

    // Invalid inputs return zero.
    check_default_zero: assert property (
        @(posedge clk) (aluc >= 5'd13) |-> (result == 32'd0)
    );

endmodule