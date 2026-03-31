module ripple_carry_adder_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [8:0] sum
);

    // Sum must equal the 8-bit addition of a and b.
    check_sum_matches_addition: assert property (
        @(posedge clk) sum == {1'b0, (a + b)}
    );

    // The least-significant sum bit must be the XOR of the least-significant input bits.
    check_lsb_sum: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0])
    );

    // The upper seven sum bits must match the 7-bit addition of the upper seven input bits.
    check_upper_bits_match: assert property (
        @(posedge clk) sum[7:1] == {1'b0, (a[7:1] + b[7:1])}
    );

    // Zero on a must pass b through to the sum.
    check_zero_a_passthrough: assert property (
        @(posedge clk) (a == 8'h00) |-> (sum == {1'b0, b})
    );

    // Zero on b must pass a through to the sum.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (b == 8'h00) |-> (sum == {1'b0, a})
    );

    // All-ones on a must produce 8'hFF plus the zero carry bit.
    check_all_ones_a: assert property (
        @(posedge clk) (a == 8'hFF) |-> (sum == 9'h1FF)
    );

    // All-ones on b must produce 8'hFF plus the zero carry bit.
    check_all_ones_b: assert property (
        @(posedge clk) (b == 8'hFF) |-> (sum == 9'h1FF)
    );

    // All-ones on both inputs must produce 8'hFE plus the zero carry bit.
    check_all_ones_ab: assert property (
        @(posedge clk) ((a == 8'hFF) && (b == 8'hFF)) |-> (sum == 9'h1FE)
    );

endmodule