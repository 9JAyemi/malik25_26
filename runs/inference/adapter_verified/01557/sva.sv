module alu_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [4:0]  aluc,
    input logic [31:0] result
);

// Addition (signed) returns the signed 32-bit sum.
    check_add_signed_result: assert property (
        @(posedge clk) (aluc == 5'd0) |-> (result == $signed(a) + $signed(b))
    );

// Addition (unsigned) returns the unsigned 32-bit sum.
    check_add_unsigned_result: assert property (
        @(posedge clk) (aluc == 5'd1) |-> (result == a + b)
    );

// Subtraction (signed) returns the signed 32-bit difference.
    check_sub_signed_result: assert property (
        @(posedge clk) (aluc == 5'd2) |-> (result == $signed(a) - $signed(b))
    );

// Subtraction (unsigned) returns the unsigned 32-bit difference.
    check_sub_unsigned_result: assert property (
        @(posedge clk) (aluc == 5'd3) |-> (result == a - b)
    );

// Bitwise AND returns the bitwise AND of the inputs.
    check_and_result: assert property (
        @(posedge clk) (aluc == 5'd4) |-> (result == a & b)
    );

// Bitwise OR returns the bitwise OR of the inputs.
    check_or_result: assert property (
        @(posedge clk) (aluc == 5'd5) |-> (result == a | b)
    );

// Bitwise XOR returns the bitwise XOR of the inputs.
    check_xor_result: assert property (
        @(posedge clk) (aluc == 5'd6) |-> (result == a ^ b)
    );

// Bitwise NOR returns the bitwise NOR of the inputs.
    check_nor_result: assert property (
        @(posedge clk) (aluc == 5'd7) |-> (result == ~(a | b))
    );

// Set Less Than (signed) returns 1 if a is signed less than b, else 0.
    check_slt_signed_result: assert property (
        @(posedge clk) (aluc == 5'd8) |-> (result == (($signed(a) < $signed(b)) ? 32'd1 : 32'd0))
    );

// Set Less Than (unsigned) returns 1 if a is unsigned less than b, else 0.
    check_slt_unsigned_result: assert property (
        @(posedge clk) (aluc == 5'd9) |-> (result == (a < b ? 32'd1 : 32'd0))
    );

// Shift Left Logical returns b shifted left by a.
    check_shift_left_logical_result: assert property (
        @(posedge clk) (aluc == 5'd10) |-> (result == b << a)
    );

// Shift Right Logical returns b shifted right by a.
    check_shift_right_logical_result: assert property (
        @(posedge clk) (aluc == 5'd11) |-> (result == b >> a)
    );

// Shift Right Arithmetic returns b signed-shifted right by a.
    check_shift_right_arithmetic_result: assert property (
        @(posedge clk) (aluc == 5'd12) |-> (result == $signed(b) >>> a)
    );

// Load Upper Immediate returns b[15:0] concatenated with 16 zeros.
    check_load_upper_immediate_result: assert property (
        @(posedge clk) (aluc == 5'd14) |-> (result == {b[15:0], 16'h0000})
    );

// Zero forces the result to zero.
    check_zero_result: assert property (
        @(posedge clk) (aluc == 5'd31) |-> (result == 32'h0000_0000)
    );

// Invalid aluc values drive the result to zero.
    check_default_result: assert property (
        @(posedge clk) (aluc >= 5'd13 && aluc <= 5'd13) |-> (result == 32'h0000_0000)
    );

endmodule
