
module nand4(Y, A, B, C, D);
    output Y;
    input A, B, C, D;
    wire nand1_out, nand2_out;

    nand2 nand1(nand1_out, A, B);
    nand2 nand2(nand2_out, C, D);
    nand2 nand3(Y, nand1_out, nand2_out);
endmodule
module nand2(Y, A, B);
    output Y;
    input A, B;

    assign Y = ~(A & B);
endmodule