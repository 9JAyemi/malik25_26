module nor_gate_using_nand(
    input a,
    input b,
    output out
);

wire temp1, temp2;

nand gate1(temp1, a, a);
nand gate2(temp2, b, b);
nand gate3(out, temp1, temp2);

endmodule