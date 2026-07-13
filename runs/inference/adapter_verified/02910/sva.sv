module top_module_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] sum
);

// The full 32-bit sum matches the RTL adder equation.
    check_full_sum_equation: assert property (
        @(posedge clk) sum == (a + b)
    );

// The lower 16 bits of sum match the lower 16-bit adder result.
    check_lower_half_sum: assert property (
        @(posedge clk) sum[15:0] == (a[15:0] + b[15:0])
    );

// The upper 16 bits of sum match the selected upper 16-bit adder result.
    check_upper_half_sum: assert property (
        @(posedge clk) sum[31:16] == (a[31:16] + b[31:16])
    );

// When the lower half carry is zero, the upper half uses the zero-carry adder.
    check_upper_half_zero_carry: assert property (
        @(posedge clk) !((a[15:0] + b[15:0]) >= 16'h10000) |-> (sum[31:16] == (a[31:16] + b[31:16]))
    );

// When the lower half carry is one, the upper half uses the one-carry adder.
    check_upper_half_one_carry: assert property (
        @(posedge clk) ((a[15:0] + b[15:0]) >= 16'h10000) |-> (sum[31:16] == (a[31:16] + b[31:16] + 16'h1))
    );

// Adding zero on b passes a through unchanged.
    check_b_zero_passthrough: assert property (
        @(posedge clk) (b == 32'h0) |-> (sum == a)
    );

// Adding zero on a passes b through unchanged.
    check_a_zero_passthrough: assert property (
        @(posedge clk) (a == 32'h0) |-> (sum == b)
    );

// Adding equal 16-bit operands with zero carry-out produces a doubled value.
    check_equal_operands_no_carry: assert property (
        @(posedge clk) ((a[15:0] == b[15:0]) && ((a[15:0] + b[15:0]) < 16'h10000)) |-> (sum == {16'h0, (a[15:0] + b[15:0]) << 1})
    );

// Adding equal 16-bit operands with carry-out produces a doubled value plus one.
    check_equal_operands_with_carry: assert property (
        @(posedge clk) ((a[15:0] == b[15:0]) && ((a[15:0] + b[15:0]) >= 16'h10000)) |-> (sum == {16'h0, (a[15:0] + b[15:0]) << 1} + 32'h1)
    );

endmodule
