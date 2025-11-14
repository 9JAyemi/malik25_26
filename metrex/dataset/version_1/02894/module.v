
module xor_nand (
    input a,
    input b,
    output out
);

    wire nand1;

    assign nand1 = ~(a & b);
    assign out = ~nand1;

endmodule
