module AND_32bit_sva (
    input logic        clk,
    input logic [31:0] out,
    input logic [31:0] A,
    input logic [31:0] B
);

    // Output must equal the bitwise AND of A and B.
    check_vector_and: assert property (
        @(posedge clk) out == (A & B)
    );

    // Output bit 0 must equal A[0] AND B[0].
    check_bit0_and: assert property (
        @(posedge clk) out[0] == (A[0] & B[0])
    );

    // Output bit 1 must equal A[1] AND B[1].
    check_bit1_and: assert property (
        @(posedge clk) out[1] == (A[1] & B[1])
    );

    // Output bit 2 must equal A[2] AND B[2].
    check_bit2_and: assert property (
        @(posedge clk) out[2] == (A[2] & B[2])
    );

    // Output bit 3 must equal A[3] AND B[3].
    check_bit3_and: assert property (
        @(posedge clk) out[3] == (A[3] & B[3])
    );

    // Output bit 4 must equal A[4] AND B[4].
    check_bit4_and: assert property (
        @(posedge clk) out[4] == (A[4] & B[4])
    );

    // Output bit 5 must equal A[5] AND B[5].
    check_bit5_and: assert property (
        @(posedge clk) out[5] == (A[5] & B[5])
    );

    // Output bit 6 must equal A[6] AND B[6].
    check_bit6_and: assert property (
        @(posedge clk) out[6] == (A[6] & B[6])
    );

    // Output bit 7 must equal A[7] AND B[7].
    check_bit7_and: assert property (
        @(posedge clk) out[7] == (A[7] & B[7])
    );

    // Output bit 8 must equal A[8] AND B[8].
    check_bit8_and: assert property (
        @(posedge clk) out[8] == (A[8] & B[8])
    );

    // Output bit 9 must equal A[9] AND B[9].
    check_bit9_and: assert property (
        @(posedge clk) out[9] == (A[9] & B[9])
    );

    // Output bit 10 must equal A[10] AND B[10].
    check_bit10_and: assert property (
        @(posedge clk) out[10] == (A[10] & B[10])
    );

    // Output bit 11 must equal A[11] AND B[11].
    check_bit11_and: assert property (
        @(posedge clk) out[11] == (A[11] & B[11])
    );

    // Output bit 12 must equal A[12] AND B[12].
    check_bit12_and: assert property (
        @(posedge clk) out[12] == (A[12] & B[12])
    );

    // Output bit 13 must equal A[13] AND B[13].
    check_bit13_and: assert property (
        @(posedge clk) out[13] == (A[13] & B[13])
    );

    // Output bit 14 must equal A[14] AND B[14].
    check_bit14_and: assert property (
        @(posedge clk) out[14] == (A[14] & B[14])
    );

    // Output bit 15 must equal A[15] AND B[15].
    check_bit15_and: assert property (
        @(posedge clk) out[15] == (A[15] & B[15])
    );

    // Output bit 16 must equal A[16] AND B[16].
    check_bit16_and: assert property (
        @(posedge clk) out[16] == (A[16] & B[16])
    );

    // Output bit 17 must equal A[17] AND B[17].
    check_bit17_and: assert property (
        @(posedge clk) out[17] == (A[17] & B[17])
    );

    // Output bit 18 must equal A[18] AND B[18].
    check_bit18_and: assert property (
        @(posedge clk) out[18] == (A[18] & B[18])
    );

    // Output bit 19 must equal A[19] AND B[19].
    check_bit19_and: assert property (
        @(posedge clk) out[19] == (A[19] & B[19])
    );

    // Output bit 20 must equal A[20] AND B[20].
    check_bit20_and: assert property (
        @(posedge clk) out[20] == (A[20] & B[20])
    );

    // Output bit 21 must equal A[21] AND B[21].
    check_bit21_and: assert property (
        @(posedge clk) out[21] == (A[21] & B[21])
    );

    // Output bit 22 must equal A[22] AND B[22].
    check_bit22_and: assert property (
        @(posedge clk) out[22] == (A[22] & B[22])
    );

    // Output bit 23 must equal A[23] AND B[23].
    check_bit23_and: assert property (
        @(posedge clk) out[23] == (A[23] & B[23])
    );

    // Output bit 24 must equal A[24] AND B[24].
    check_bit24_and: assert property (
        @(posedge clk) out[24] == (A[24] & B[24])
    );

    // Output bit 25 must equal A[25] AND B[25].
    check_bit25_and: assert property (
        @(posedge clk) out[25] == (A[25] & B[25])
    );

    // Output bit 26 must equal A[26] AND B[26].
    check_bit26_and: assert property (
        @(posedge clk) out[26] == (A[26] & B[26])
    );

    // Output bit 27 must equal A[27] AND B[27].
    check_bit27_and: assert property (
        @(posedge clk) out[27] == (A[27] & B[27])
    );

    // Output bit 28 must equal A[28] AND B[28].
    check_bit28_and: assert property (
        @(posedge clk) out[28] == (A[28] & B[28])
    );

    // Output bit 29 must equal A[29] AND B[29].
    check_bit29_and: assert property (
        @(posedge clk) out[29] == (A[29] & B[29])
    );

    // Output bit 30 must equal A[30] AND B[30].
    check_bit30_and: assert property (
        @(posedge clk) out[30] == (A[30] & B[30])
    );

    // Output bit 31 must equal A[31] AND B[31].
    check_bit31_and: assert property (
        @(posedge clk) out[31] == (A[31] & B[31])
    );

endmodule