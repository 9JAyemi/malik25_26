module nor_gate (
    input a,
    input b,
    output out
);

wire nand1_out, nand2_out;

nand nand1 (nand1_out, a, a);
nand nand2 (nand2_out, b, b);
nand nand3 (out, nand1_out, nand2_out);

endmodule