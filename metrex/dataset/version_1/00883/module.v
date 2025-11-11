
module binary_to_3bit_decoder (
    input wire [2:0] in,
    output wire o0,
    output wire o1,
    output wire o2
);

assign o0 = in[0];
assign o1 = in[1];
assign o2 = in[2];

endmodule
module nor_gate_using_nand (
    input wire a,
    input wire b,
    output wire out
);

assign out = !(a & b);

endmodule
module top_module (
    input wire [2:0] vec,
    input wire a,
    input wire b,
    output wire out
);

wire o0, o1, o2;

binary_to_3bit_decoder decoder(vec, o0, o1, o2);
nor_gate_using_nand nor_gate(o0, o1, out);

endmodule