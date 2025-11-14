module nor_using_nand(
    input a,
    input b,
    output out
);

wire nand1_out, nand2_out;

nand nand1(nand1_out, a, b);
nand nand2(nand2_out, nand1_out, nand1_out);
not not1(out, nand2_out);

endmodule