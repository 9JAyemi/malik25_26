
module nor_gate(
    input a,
    input b,
    output out
);

wire nand1_out;
wire nand2_out;
wire not_out;

nand nand1(nand1_out, a, a);
nand nand2(nand2_out, b, b);
not not1(not_out, nand1_out);
nand nand3(out, nand2_out, not_out);

endmodule
