module ripple_adder_32_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        cin,
    input logic [31:0] sum,
    input logic        cout
);

// Sum bit 0 matches the first full-adder XOR equation.
    check_sum_bit0: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

// Sum bit 1 uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) sum[1] == (a[1] ^ b[1] ^ carry_bit(a[0], b[0], cin))
    );

// Sum bit 2 uses the carry generated from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) sum[2] == (a[2] ^ b[2] ^ carry_bit(a[1], b[1], carry_bit(a[0], b[0], cin)))
    );

// Sum bit 3 uses the carry generated from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) sum[3] == (a[3] ^ b[3] ^ carry_bit(a[2], b[2], carry_bit(a[1], b[1], carry_bit(a[0], b[0], cin))))
    );

// Sum bit 4 uses the carry generated from bit 3.
    check_sum_bit4: assert property (
        @(posedge clk) sum[4] == (a[4] ^ b[4] ^ carry_bit(a[3], b[3], carry_bit(a[2], b[2], carry_bit(a[1], b[1], carry_bit(a[0], b[0], cin)))))
    );

// Sum bit 5 uses the carry generated from bit 4.
    check_sum_bit5: assert property (
        @(posedge clk) sum[5] == (a[5] ^ b[5] ^ carry_bit(a[4], b[4], carry_bit(a[3], b[3], carry_bit(a[2], b[2], carry_bit(a[1], b[1], carry_bit(a[0], b[0], cin))))))
    );

// Sum bit 6 uses the carry generated from bit 5.
    check_sum_bit6: assert property (
        @(posedge clk) sum[6] == (a[6] ^ b[6] ^ carry_bit(a[5], b[5], carry_bit(a[4], b[4], carry_bit(a[3], b[3], carry_bit(a[2], b[2], carry_bit(a[1], b[1], carry_bit(a[0], b[0], cin))))))
    );

// Sum bit 7 uses the carry generated from bit 6.
    check_sum_bit7: assert property (
        @(posedge clk) sum[7] == (a[7] ^ b[7] ^ carry_bit(a[6], b[6], carry_bit(a[5], b[5], carry_bit(a[4], b[4], carry_bit(a[3], b[3], carry_bit(a[2], b[2], carry_bit(a[1], b[1], carry_bit(a[0], b[0], cin))))))
    );

// Sum bit 8 uses the carry generated from bit 7.
    check_sum_bit8: assert property (
        @(posedge clk) sum[8] == (a[8] ^ b[8] ^ carry_bit(a[7], b[7], carry_bit(a[6], b[6], carry_bit(a[5], b[5], carry_bit(a[4], b[4], carry_bit(a[3], b[3], carry_bit(a[2], b[2], carry_bit(a[1], b[1], carry_bit(a[0], b[0], cin))))))
    );

// Sum bit 9 uses the carry generated from bit 8.
    check_sum_bit9: assert property (
        @(posedge clk) sum[9] == (a[9] ^ b[9] ^ carry_bit(a[8], b[8], carry_bit(a[7], b[7], carry_bit(a[6], b[6], carry_bit(a[5], b[5], carry_bit(a[4], b[4], carry_bit(a[3], b[3], carry_bit(a[2], b[2], carry_bit(a[1], b[1], carry_bit(a[0], b[0], cin))))))
    );

// Sum bit 10 uses the carry generated from bit 9.
    check_sum_bit10: assert property (
        @(posedge clk) sum[10] == (a[10] ^ b[10] ^ carry_bit(a[9], b[9], carry_bit(a[8], b[8], carry_bit(a[7], b[7], carry_bit(a[6], b[6], carry_bit(a[5], b[5], carry_bit(a[4], b[4], carry_bit(a[3], b[3], carry_bit(a[2], b[2], carry_bit(a[1], b[1], carry_bit(a[0], b[0], cin))))))
    );

// Sum bit 11 uses the carry generated from bit 10.
    check_sum_bit11: assert property (
        @(posedge clk) sum[11] == (a[11] ^ b[11] ^ carry_bit(a[10], b[10], carry_bit(a[9], b[9], carry_bit(a[8], b[8], carry_bit(a[7], b[7], carry_bit(a[6], b[6], carry_bit(a[5], b[5], carry_bit(a[4], b[4], carry_bit(a[3], b[3], carry_bit(a[2], b[2], carry_bit(a[1], b[1], carry_bit(a[0], b[0], cin))))))
    );

// Sum bit 12 uses the carry generated from bit 11.
    check_sum_bit12: assert property (
        @(posedge clk) sum[12] == (a[12] ^ b[12] ^ carry_bit(a[11], b[11], carry_bit(a[10], b[10], carry_bit(a[9], b[9], carry_bit(a[8], b[8], carry_bit(a[7], b[7], carry_bit(a[6], b[6], carry_bit(a[5], b[5], carry_bit(a[4], b[4], carry_bit(a[3], b[3], carry_bit(a[2], b[2], carry_bit(a[1], b[1], carry_bit(a[0], b[0], cin))))))
    );

// Sum bit 13 uses the carry generated from bit 12.
    check_sum_bit13: assert property (
        @(posedge clk) sum[13] == (a[13] ^ b[13] ^ carry_bit(a[12], b[12], carry_bit(a[11], b[11], carry_bit(a[10], b[10], carry_bit(a[9], b[9], carry_bit(a[8], b[8], carry_bit(a[7], b[7], carry_bit(a[6], b[6], carry_bit(a[5], b[5], carry_bit(a[4], b[4], carry_bit(a[3], b[3], carry_bit(a[2], b[2], carry_bit(a[1], b[1], carry_bit(a[0], b[0], cin))))))
    );

// Sum bit 14 uses the carry generated from bit 13.
    check_sum_bit14: assert property (
        @(posedge clk) sum[14] == (a[14] ^ b[14] ^ carry_bit(a[13], b[13], carry_bit(a[12], b[12], carry_bit(a[11], b[11], carry_bit(a[10], b[10], carry_bit(a[9], b[9], carry_bit(a[8], b[8], carry_bit(a[7], b[7], carry_bit(a[6], b[6], carry_bit(a[5], b[5], carry_bit(a[4], b[4], carry_bit(a[3], b[3], carry_bit(a[2], b[2], carry_bit(a[1], b[1], carry_bit(a[0], b[0], cin))))))
    );

// Sum bit 15 uses the carry generated from bit 14.
    check_sum_bit15: assert property (
        @(posedge clk) sum[15] == (a[15] ^ b[15] ^ carry_bit(a[14], b[14], carry_bit(a[13], b[13], carry_bit(a[12], b[12], carry_bit(a[11], b[11], carry_bit(a[10], b[10], carry_bit(a[9], b[9], carry_bit(a[8], b[8], carry_bit(a[7], b[7], carry