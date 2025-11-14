module nand4 (
    input A,
    input B,
    input C,
    input D,
    output Y
);

    wire nand1_out, nand2_out;

    nand2 nand1(.A(A), .B(B), .Y(nand1_out));
    nand2 nand2(.A(C), .B(D), .Y(nand2_out));
    nand2 nand3(.A(nand1_out), .B(nand2_out), .Y(Y)); 

endmodule

module nand2(
    input A,
    input B,
    output Y
);

assign Y = ~(A & B);

endmodule
