module top_module_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] sum
);

    // Low 16 bits are the zero-extended low sum.
    check_low_sum_zero_extended: assert property (
        @(posedge clk) sum[15:0] == {16'h0000, (a[15:0] + b[15:0])}
    );

    // High 16 bits are the zero-extended high sum.
    check_high_sum_zero_extended: assert property (
        @(posedge clk) sum[31:16] == {16'h0000, (a[31:16] + b[31:16])}
    );

    // The full 32-bit output is the zero-extended 32-bit addition.
    check_full_sum_zero_extended: assert property (
        @(posedge clk) sum == {16'h0000, (a + b)}
    );

    // The low 16-bit sum matches the low 16 bits of the 32-bit addition.
    check_low_sum_matches_addition: assert property (
        @(posedge clk) sum[15:0] == (a[15:0] + b[15:0])
    );

    // The high 16-bit sum matches the high 16 bits of the 32-bit addition.
    check_high_sum_matches_addition: assert property (
        @(posedge clk) sum[31:16] == (a[31:16] + b[31:16])
    );

    // Zero on both inputs produces zero on the output.
    check_zero_inputs_zero_output: assert property (
        @(posedge clk) ((a == 32'h0000_0000) && (b == 32'h0000_0000)) |-> (sum == 32'h0000_0000)
    );

    // Zero on the low input passes the high input through.
    check_low_zero_passthrough: assert property (
        @(posedge clk) (a[15:0] == 16'h0000) |-> (sum == {16'h0000, b[31:16], (a[31:16] + b[31:16])})
    );

    // Zero on the high input passes the low input through.
    check_high_zero_passthrough: assert property (
        @(posedge clk) (a[31:16] == 16'h0000) |-> (sum == {16'h0000, a[15:0], (a[15:0] + b[15:0])})
    );

    // Adding one to zero on the low input increments the high input by one.
    check_low_one_plus_zero: assert property (
        @(posedge clk) ((a[15:0] == 16'h0001) && (b[15:0] == 16'h0000)) |-> (sum == {16'h0000, (a[31:16] + 16'h0001), (a[31:16] + b[31:16])})
    );

    // Adding one to zero on the high input increments the low input by one.
    check_high_one_plus_zero: assert property (
        @(posedge clk) ((a[31:16] == 16'h0001) && (b[31:16] == 16'h0000)) |-> (sum == {16'h0000, (a[15:0] + 16'h0001), (a[15:0] + b[15:0])})
    );

endmodule