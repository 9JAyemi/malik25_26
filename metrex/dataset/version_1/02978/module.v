module and_gate(
    input a,
    input b,
    output out
);

wire nand_out;
wire inv_out;

nand_gate nand1(a, b, nand_out);
inverter inv1(nand_out, inv_out);
assign out = inv_out;

endmodule

module nand_gate(
    input a,
    input b,
    output out
);

assign out = ~(a & b);

endmodule

module inverter(
    input in,
    output out
);

assign out = ~in;

endmodule