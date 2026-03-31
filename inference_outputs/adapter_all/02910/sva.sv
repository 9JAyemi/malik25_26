module top_module_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] sum
);

    // No RTL clock or reset; clk is an external sampling clock for SVA.

    // The full 32-bit sum must equal the arithmetic addition of a and b.
    check_full_addition: assert property (
        @(posedge clk) sum == (a + b)
    );

    // The low 16 bits of sum must equal the low 16 bits of a plus b.
    check_lower_half_addition: assert property (
        @(posedge clk) sum[15:0] == (a[15:0] + b[15:0])
    );

    // The high 16 bits of sum must equal the high 16 bits of a plus b.
    check_upper_half_addition: assert property (
        @(posedge clk) sum[31:16] == (a[31:16] + b[31:16])
    );

    // Adding zero on b must pass a through unchanged.
    check_add_zero_b: assert property (
        @(posedge clk) (b == 32'h0000_0000) |-> (sum == a)
    );

    // Adding zero on a must pass b through unchanged.
    check_add_zero_a: assert property (
        @(posedge clk) (a == 32'h0000_0000) |-> (sum == b)
    );

    // Adding equal operands must double them and truncate to 32 bits.
    check_double_equal_operands: assert property (
        @(posedge clk) (a == b) |-> (sum == (a << 1))
    );

    // Zero plus zero must produce zero.
    check_zero_plus_zero: assert property (
        @(posedge clk) ((a == 32'h0000_0000) && (b == 32'h0000_0000)) |-> (sum == 32'h0000_0000)
    );

    // All-ones plus all-ones must produce 0xFFFF_FFFE.
    check_all_ones_plus_all_ones: assert property (
        @(posedge clk) ((a == 32'hFFFF_FFFF) && (b == 32'hFFFF_FFFF)) |-> (sum == 32'hFFFF_FFFE)
    );

    // Adding 1 to 0xFFFF_FFFF must wrap to 0xFFFF_FFFE.
    check_overflow_case: assert property (
        @(posedge clk) ((a == 32'hFFFF_FFFF) && (b == 32'h0000_0001)) |-> (sum == 32'hFFFF_FFFE)
    );

endmodule