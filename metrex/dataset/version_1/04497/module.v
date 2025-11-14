
module six_to_one_rtl (
    input [4:0] A,
    input [1:0] B,
    output [7:0] X
);

    wire [3:0] sum1, sum2;

    nand (sum1[0], A[0], A[1]);
    nand (sum1[1], A[0], A[2]);
    nand (sum1[2], A[1], A[2]);
    nor (sum1[3], A[0], A[1]);

    nand (sum2[0], B[0], B[1]);
    nand (sum2[1], B[0], sum1[3]);
    nor (sum2[2], B[1], sum1[3]);

    nand (X[0], A[3], A[4]);
    nand (X[1], A[3], sum2[2]);
    nor (X[2], A[4], sum2[2]);

    nand (X[3], sum1[2], sum2[1]);
    nand (X[4], sum1[2], sum2[0]);
    nand (X[5], sum1[1], sum2[1]);
    nand (X[6], sum1[1], sum2[0]);

    nor (X[7], sum1[0], sum2[1]);
endmodule