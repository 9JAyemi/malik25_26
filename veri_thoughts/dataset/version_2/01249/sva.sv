module GDA_St_N8_M8_P1_sva (
    input logic clk,
    input logic reset_n,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [8:0] res,
    input logic [2:0] temp1,
    input logic [2:0] temp2,
    input logic [2:0] temp3,
    input logic [2:0] temp4,
    input logic [2:0] temp5,
    input logic [2:0] temp6,
    input logic [2:0] temp7,
    input logic [2:0] temp8,
    input logic p0,
    input logic p1,
    input logic p2,
    input logic p3,
    input logic p4,
    input logic p5,
    input logic p6,
    input logic g0,
    input logic g1,
    input logic g2,
    input logic g3,
    input logic g4,
    input logic g5,
    input logic g6,
    input logic c1,
    input logic c2,
    input logic c3,
    input logic c4,
    input logic c5,
    input logic c6,
    input logic c7
);
    // g[i] equals in1[i] & in2[i] for bits 0..6.
    check_generate_bits: assert property (
        @(posedge clk) disable iff (!reset_n)
        (g0 == (in1[0] & in2[0])) &&
        (g1 == (in1[1] & in2[1])) &&
        (g2 == (in1[2] & in2[2])) &&
        (g3 == (in1[3] & in2[3])) &&
        (g4 == (in1[4] & in2[4])) &&
        (g5 == (in1[5] & in2[5])) &&
        (g6 == (in1[6] & in2[6]))
    );

    // p[i] equals in1[i] ^ in2[i] for bits 0..6.
    check_propagate_bits: assert property (
        @(posedge clk) disable iff (!reset_n)
        (p0 == (in1[0] ^ in2[0])) &&
        (p1 == (in1[1] ^ in2[1])) &&
        (p2 == (in1[2] ^ in2[2])) &&
        (p3 == (in1[3] ^ in2[3])) &&
        (p4 == (in1[4] ^ in2[4])) &&
        (p5 == (in1[5] ^ in2[5])) &&
        (p6 == (in1[6] ^ in2[6]))
    );

    // c[i] equals g[i-1] for i=1..7.
    check_carry_mapping_c_eq_g: assert property (
        @(posedge clk) disable iff (!reset_n)
        (c1 == g0) && (c2 == g1) && (c3 == g2) &&
        (c4 == g3) && (c5 == g4) && (c6 == g5) && (c7 == g6)
    );

    // temp1 is the 1-bit addition result of in1[0] + in2[0].
    check_temp1_add: assert property (
        @(posedge clk) disable iff (!reset_n)
        (temp1[0] == p0) && (temp1[1] == g0)
    );

    // temp2 is in1[1] + in2[1] + c1 (sum and carry).
    check_temp2_add3bits: assert property (
        @(posedge clk) disable iff (!reset_n)
        (temp2[0] == (p1 ^ c1)) && (temp2[1] == (g1 | (p1 & c1)))
    );

    // temp3 is in1[2] + in2[2] + c2 (sum and carry).
    check_temp3_add3bits: assert property (
        @(posedge clk) disable iff (!reset_n)
        (temp3[0] == (p2 ^ c2)) && (temp3[1] == (g2 | (p2 & c2)))
    );

    // temp4 is in1[3] + in2[3] + c3 (sum and carry).
    check_temp4_add3bits: assert property (
        @(posedge clk) disable iff (!reset_n)
        (temp4[0] == (p3 ^ c3)) && (temp4[1] == (g3 | (p3 & c3)))
    );

    // temp5 is in1[4] + in2[4] + c4 (sum and carry).
    check_temp5_add3bits: assert property (
        @(posedge clk) disable iff (!reset_n)
        (temp5[0] == (p4 ^ c4)) && (temp5[1] == (g4 | (p4 & c4)))
    );

    // temp6 is in1[5] + in2[5] + c5 (sum and carry).
    check_temp6_add3bits: assert property (
        @(posedge clk) disable iff (!reset_n)
        (temp6[0] == (p5 ^ c5)) && (temp6[1] == (g5 | (p5 & c5)))
    );

    // temp7 is in1[6] + in2[6] + c6 (sum and carry).
    check_temp7_add3bits: assert property (
        @(posedge clk) disable iff (!reset_n)
        (temp7[0] == (p6 ^ c6)) && (temp7[1] == (g6 | (p6 & c6)))
    );

    // temp8 is in1[7] + in2[7] + c7 (sum and carry).
    check_temp8_add3bits: assert property (
        @(posedge clk) disable iff (!reset_n)
        (temp8[0] == ((in1[7] ^ in2[7]) ^ c7)) &&
        (temp8[1] == ((in1[7] & in2[7]) | ((in1[7] ^ in2[7]) & c7)))
    );

    // res is concatenation of temp bits per RTL mapping.
    check_res_concatenation: assert property (
        @(posedge clk) disable iff (!reset_n)
        res == {temp8[1:0], temp7[0], temp6[0], temp5[0], temp4[0], temp3[0], temp2[0], temp1[0]}
    );
endmodule