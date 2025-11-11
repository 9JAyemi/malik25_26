
module xnor_gate(
    input a,
    input b,
    output out
);

wire nand_out, nor_out;

nand_gate nand1(a, b, nand_out);
nor_gate nor1(a, b, nor_out);
nand_gate nand2(nand_out, nor_out, out);

endmodule
module nand_gate(
    input a,
    input b,
    output out
);

assign out = ~(a & b);

endmodule
module nor_gate(
    input a,
    input b,
    output out
);

assign out = ~(a | b);

endmodule
module top_module( 
    input [3:0] in,
    output out
);

wire xnor_out1, xnor_out2;

xnor_gate xnor1(in[0], in[1], xnor_out1);
xnor_gate xnor2(in[2], in[3], xnor_out2);
xnor_gate xnor3(xnor_out1, xnor_out2, out);

endmodule