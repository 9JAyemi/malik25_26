module nand2(
    input  A,
    input  B,
    output Y
);
    assign Y = ~(A & B);
endmodule

module nand4(
    input  A,
    input  B,
    input  C,
    input  D,
    output Y
);
    wire w1, w2, w3;
    nand2 n1(A, B, w1);
    nand2 n2(C, D, w2);
    nand2 n3(w1, w2, w3);
    nand2 n4(w3, w3, Y);
endmodule