module full_adder_1bit (
    output sum,
    output carry,
    input a,
    input b,
    input c
);

    wire w1, w2, w3;

    nand n1 (w1, a, b, c);
    nand n2 (w2, w1, c, b);
    nand n3 (w3, w1, c, a);
    nand n4 (sum, w2, w3, c);
    nand n5 (carry, w1, c, a);

endmodule

module nand_adder_4bit (
    output [3:0] S,
    output C_out,
    input [3:0] A,
    input [3:0] B,
    input C_in
);

    wire c0, c1, c2, c3, s0, s1, s2, s3;

    full_adder_1bit fa0 (s0, c0, A[0], B[0], C_in);
    full_adder_1bit fa1 (s1, c1, A[1], B[1], c0);
    full_adder_1bit fa2 (s2, c2, A[2], B[2], c1);
    full_adder_1bit fa3 (s3, c3, A[3], B[3], c2);

    assign S = {s3, s2, s1, s0};
    assign C_out = c3;

endmodule