module ripple_carry_adder_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [8:0] sum
);

// sum[7:0] equals a + b (8-bit wrap).
    check_sum_matches_addition: assert property (
        @(posedge clk) sum[7:0] == (a + b)
    );

// LSB sum equals a[0] ^ b[0] ^ cin[0].
    check_lsb_sum: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ 1'b0)
    );

// Bit1 sum equals a[1] ^ b[1] ^ carry[0].
    check_bit1_sum: assert property (
        @(posedge clk) sum[1] == (a[1] ^ b[1] ^ carry0)
    );

// Bit2 sum equals a[2] ^ b[2] ^ carry[1].
    check_bit2_sum: assert property (
        @(posedge clk) sum[2] == (a[2] ^ b[2] ^ carry1)
    );

// Bit3 sum equals a[3] ^ b[3] ^ carry[2].
    check_bit3_sum: assert property (
        @(posedge clk) sum[3] == (a[3] ^ b[3] ^ carry2)
    );

// Bit4 sum equals a[4] ^ b[4] ^ carry[3].
    check_bit4_sum: assert property (
        @(posedge clk) sum[4] == (a[4] ^ b[4] ^ carry3)
    );

// Bit5 sum equals a[5] ^ b[5] ^ carry[4].
    check_bit5_sum: assert property (
        @(posedge clk) sum[5] == (a[5] ^ b[5] ^ carry4)
    );

// Bit6 sum equals a[6] ^ b[6] ^ carry[5].
    check_bit6_sum: assert property (
        @(posedge clk) sum[6] == (a[6] ^ b[6] ^ carry5)
    );

// Bit7 sum equals a[7] ^ b[7] ^ carry[6].
    check_bit7_sum: assert property (
        @(posedge clk) sum[7] == (a[7] ^ b[7] ^ carry6)
    );

// Bit8 sum equals carry[7].
    check_bit8_sum: assert property (
        @(posedge clk) sum[8] == carry7
    );

// No carry-out implies sum equals a + b (no wrap).
    check_no_carry_no_wrap: assert property (
        @(posedge clk) !carry7 |-> (sum[7:0] == (a + b))
    );

// Carry-out implies sum equals a + b + 1 (8-bit wrap).
    check_carry_wrap: assert property (
        @(posedge clk) carry7 |-> (sum[7:0] == (a + b + 8'd1))
    );

endmodule
