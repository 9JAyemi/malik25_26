module alu_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [4:0]  aluc,
    input logic [31:0] result
);

    // Addition (signed) returns the 32-bit sum.
    check_add_signed_result: assert property (
        @(posedge clk) (aluc == 5'd0) |-> (result == (a + b))
    );

    // Addition (unsigned) returns the 32-bit sum.
    check_add_unsigned_result: assert property (
        @(posedge clk) (aluc == 5'd1) |-> (result == (a + b))
    );

    // Subtraction (signed) returns the 32-bit difference.
    check_sub_signed_result: assert property (
        @(posedge clk) (aluc == 5'd2) |-> (result == (a - b))
    );

    // Subtraction (unsigned) returns the 32-bit difference.
    check_sub_unsigned_result: assert property (
        @(posedge clk) (aluc == 5'd3) |-> (result == (a - b))
    );

    // Bitwise AND returns the 32-bit AND result.
    check_and_result: assert property (
        @(posedge clk) (aluc == 5'd4) |-> (result == (a & b))
    );

    // Bitwise OR returns the 32-bit OR result.
    check_or_result: assert property (
        @(posedge clk) (aluc == 5'd5) |-> (result == (a | b))
    );

    // Bitwise XOR returns the 32-bit XOR result.
    check_xor_result: assert property (
        @(posedge clk) (aluc == 5'd6) |-> (result == (a ^ b))
    );

    // Bitwise NOR returns the 32-bit NOR result.
    check_nor_result: assert property (
        @(posedge clk) (aluc == 5'd7) |-> (result == ~(a | b))
    );

    // Set Less Than (signed) returns the signed comparison result.
    check_slt_signed_result: assert property (
        @(posedge clk) (aluc == 5'd8) |-> (result == ((a[31] ^ b[31]) ? (a[31] ? 32'd1 : 32'd0) : (a < b)))
    );

    // Set Less Than (unsigned) returns the unsigned comparison result.
    check_slt_unsigned_result: assert property (
        @(posedge clk) (aluc == 5'd9) |-> (result == (a < b))
    );

    // Shift Left Logical returns the 32-bit left shift result.
    check_shift_left_logical_result: assert property (
        @(posedge clk) (aluc == 5'd10) |-> (result == (b << a))
    );

    // Shift Right Logical returns the 32-bit right shift result.
    check_shift_right_logical_result: assert property (
        @(posedge clk) (aluc == 5'd11) |-> (result == (b >> a))
    );

    // Shift Right Arithmetic returns the 32-bit arithmetic right shift result.
    check_shift_right_arithmetic_result: assert property (
        @(posedge clk) (aluc == 5'd12) |-> (result == ($signed(b) >>> a))
    );

    // Load Upper Immediate returns the upper 16 bits of b with zeros in the lower 16 bits.
    check_load_upper_immediate_result: assert property (
        @(posedge clk) (aluc == 5'd14) |-> (result == {b[15:0], 16'b0})
    );

    // Zero returns zero.
    check_zero_result: assert property (
        @(posedge clk) (aluc == 5'd31) |-> (result == 32'd0)
    );

    // Invalid opcodes return zero.
    check_default_result: assert property (
        @(posedge clk) (aluc >= 5'd13 && aluc <= 5'd13) |-> (result == 32'd0)
    );

endmodule