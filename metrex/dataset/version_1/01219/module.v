module nand2 (
    output Y,
    input A,
    input B
);

    // NAND gate
    assign Y = ~(A & B);

endmodule
