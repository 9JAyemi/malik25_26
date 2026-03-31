module zbroji_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] sum
);

// Sum must equal the 32-bit addition of a and b.
    check_sum_matches_addition: assert property (
        @(posedge clk) sum == (a + b)
    );

// Bit 0 of sum must be the XOR of the LSBs of a and b.
    check_lsb_xor: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0])
    );

// Bit 1 of sum must include the carry generated from bit 0.
    check_bit1_with_carry: assert property (
        @(posedge clk) sum[1] == (a[1] ^ b[1] ^ ((a[0] & b[0]) | (a[0] & ~b[0]) | (~a[0] & b[0])))
    );

// Bit 31 must include the carry generated from bit 30.
    check_msb_with_carry: assert property (
        @(posedge clk) sum[31] == (a[31] ^ b[31] ^ ((a[30] & b[30]) | (a[30] & ~b[30]) | (~a[30] & b[30])))
    );

endmodule
