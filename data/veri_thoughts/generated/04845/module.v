
module and_gate_using_nand(
    input a,
    input b,
    output out
);

    wire nand1_out;

    nand nand1(nand1_out, a, b);
    nand nand2(out, nand1_out, nand1_out);

endmodule
module top_module(
    input a,
    input b,
    output out
);

    and_gate_using_nand and_gate(.a(a), .b(b), .out(out));

endmodule