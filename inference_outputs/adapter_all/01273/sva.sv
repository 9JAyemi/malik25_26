module top_module_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] sum
);

    // Low 16-bit sum matches the low 16-bit addition of a and b.
    check_low_sum_matches_addition: assert property (
        @(posedge clk) sum[15:0] == (a[15:0] + b[15:0])
    );

    // High 16-bit sum matches the low 16-bit addition of the high halves plus carry-in.
    check_high_sum_matches_addition_with_cin: assert property (
        @(posedge clk) sum[31:16] == (a[31:16] + b[31:16] + (a[15:0] + b[15:0])[16])
    );

    // Carry-out is never asserted by the RTL.
    check_cout_is_zero: assert property (
        @(posedge clk) sum[32] == 1'b0
    );

    // The full 33-bit output matches the 17-bit addition of a and b.
    check_full_sum_matches_addition: assert property (
        @(posedge clk) sum == {1'b0, (a + b)}
    );

    // Adding zero on b passes a through with zero carry-out.
    check_add_zero_on_b: assert property (
        @(posedge clk) (b == 32'h0000_0000) |-> (sum == {1'b0, a})
    );

    // Adding zero on a passes b through with zero carry-out.
    check_add_zero_on_a: assert property (
        @(posedge clk) (a == 32'h0000_0000) |-> (sum == {1'b0, b})
    );

    // Zero plus zero produces zero with zero carry-out.
    check_zero_plus_zero: assert property (
        @(posedge clk) ((a == 32'h0000_0000) && (b == 32'h0000_0000)) |-> (sum == 33'h0000_0000)
    );

    // Maximum plus maximum produces 0xFFFF_FFFE with zero carry-out.
    check_max_plus_max: assert property (
        @(posedge clk) ((a == 32'hFFFF_FFFF) && (b == 32'hFFFF_FFFF)) |-> (sum == 33'hFFFF_FFFE)
    );

endmodule