module hamming_encoder_sva (
    input logic clk,
    input logic [10:0] d,
    input logic [14:0] c
);
    // c[2] must mirror d[0].
    check_c2_equals_d0: assert property (
        @(posedge clk) disable iff (1'b0) c[2] == d[0]
    );
    // c[4] must mirror d[1].
    check_c4_equals_d1: assert property (
        @(posedge clk) disable iff (1'b0) c[4] == d[1]
    );
    // c[5] must mirror d[2].
    check_c5_equals_d2: assert property (
        @(posedge clk) disable iff (1'b0) c[5] == d[2]
    );
    // c[6] must mirror d[3].
    check_c6_equals_d3: assert property (
        @(posedge clk) disable iff (1'b0) c[6] == d[3]
    );
    // c[8] must mirror d[4].
    check_c8_equals_d4: assert property (
        @(posedge clk) disable iff (1'b0) c[8] == d[4]
    );
    // c[9] must mirror d[5].
    check_c9_equals_d5: assert property (
        @(posedge clk) disable iff (1'b0) c[9] == d[5]
    );
    // c[10] must mirror d[6].
    check_c10_equals_d6: assert property (
        @(posedge clk) disable iff (1'b0) c[10] == d[6]
    );
    // c[11] must mirror d[7].
    check_c11_equals_d7: assert property (
        @(posedge clk) disable iff (1'b0) c[11] == d[7]
    );
    // c[12] must mirror d[8].
    check_c12_equals_d8: assert property (
        @(posedge clk) disable iff (1'b0) c[12] == d[8]
    );
    // c[13] must mirror d[9].
    check_c13_equals_d9: assert property (
        @(posedge clk) disable iff (1'b0) c[13] == d[9]
    );
    // c[14] must mirror d[10].
    check_c14_equals_d10: assert property (
        @(posedge clk) disable iff (1'b0) c[14] == d[10]
    );

    // c[0] parity equals d[0]^d[1]^d[3]^d[4]^d[6]^d[8]^d[10].
    check_c0_parity_p0: assert property (
        @(posedge clk) disable iff (1'b0) c[0] == (d[0] ^ d[1] ^ d[3] ^ d[4] ^ d[6] ^ d[8] ^ d[10])
    );
    // c[1] parity equals d[0]^d[2]^d[3]^d[5]^d[6]^d[9]^d[10].
    check_c1_parity_p1: assert property (
        @(posedge clk) disable iff (1'b0) c[1] == (d[0] ^ d[2] ^ d[3] ^ d[5] ^ d[6] ^ d[9] ^ d[10])
    );
    // c[3] parity equals d[1]^d[2]^d[3]^d[7]^d[8]^d[9]^d[10].
    check_c3_parity_p2: assert property (
        @(posedge clk) disable iff (1'b0) c[3] == (d[1] ^ d[2] ^ d[3] ^ d[7] ^ d[8] ^ d[9] ^ d[10])
    );
    // c[7] parity equals d[4]^d[5]^d[6]^d[7]^d[8]^d[9]^d[10].
    check_c7_parity_p3: assert property (
        @(posedge clk) disable iff (1'b0) c[7] == (d[4] ^ d[5] ^ d[6] ^ d[7] ^ d[8] ^ d[9] ^ d[10])
    );
endmodule