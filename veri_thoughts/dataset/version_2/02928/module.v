module combinational_circuit(
    input [3:0] in,
    output out_and,
    output out_or,
    output out_xor
);

wire [1:0] mux_out_and;
wire [1:0] mux_out_or;
wire [1:0] mux_out_xor;

assign mux_out_and[0] = in[0] & in[1];
assign mux_out_and[1] = in[2] & in[3];

assign mux_out_or[0] = in[0] | in[1];
assign mux_out_or[1] = in[2] | in[3];

assign mux_out_xor[0] = in[0] ^ in[1];
assign mux_out_xor[1] = in[2] ^ in[3];

assign out_and = mux_out_and[0] & mux_out_and[1];
assign out_or = mux_out_or[0] | mux_out_or[1];
assign out_xor = mux_out_xor[0] ^ mux_out_xor[1];

endmodule

module top_module( 
    input [3:0] in,
    output out_and,
    output out_or,
    output out_xor
);

combinational_circuit cc(
    .in(in),
    .out_and(out_and),
    .out_or(out_or),
    .out_xor(out_xor)
);

endmodule