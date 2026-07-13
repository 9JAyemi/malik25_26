module zbroji_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] sum
);

    // sum must equal the 32-bit addition of a and b.
    check_sum_matches_addition: assert property (
        @(posedge clk) sum == (a + b)
    );

    // Adding zero on b must pass a through unchanged.
    check_add_zero_on_b: assert property (
        @(posedge clk) (b == 32'h0000_0000) |-> (sum == a)
    );

    // Adding zero on a must pass b through unchanged.
    check_add_zero_on_a: assert property (
        @(posedge clk) (a == 32'h0000_0000) |-> (sum == b)
    );

    // The least-significant bit of sum must be the XOR of the LSBs of a and b.
    check_lsb_xor: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0])
    );

    // If both inputs are stable, the output must remain stable.
    check_stable_inputs_keep_sum_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> $stable(sum)
    );

endmodule