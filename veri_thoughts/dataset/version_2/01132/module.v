
module XOR2_NAND(
    input A,
    input B,
    output Y
);

    wire n1, n2, n3, n4;

    nand (n1, A, B);
    nand (n2, A, n1);
    nand (n3, n1, B);
    nand (Y, n2, n3);

endmodule
