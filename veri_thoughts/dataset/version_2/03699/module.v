module xor3 (
    output Y,
    input A,
    input B,
    input C
);

    wire nand1_out, nand2_out, nand3_out;

    nand nand1 (nand1_out, A, B);
    nand nand2 (nand2_out, nand1_out, C);
    nand nand3 (Y, nand2_out, nand2_out);

endmodule