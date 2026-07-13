module pipelined_circuit(
    input [3:0] in,
    output out_and,
    output out_or,
    output out_xor
);

wire [3:0] stage1_out;
wire [2:0] stage2_out;

// Stage 1
assign stage1_out[0] = in[0] & in[1];
assign stage1_out[1] = in[2] & in[3];
assign stage1_out[2] = stage1_out[0] | stage1_out[1];
assign stage1_out[3] = stage1_out[0] ^ stage1_out[1];

// Stage 2
assign stage2_out[0] = stage1_out[0] & stage1_out[1];
assign stage2_out[1] = stage1_out[2] | stage1_out[3];
assign stage2_out[2] = stage1_out[2] ^ stage1_out[3];

// Output
assign out_and = stage2_out[0];
assign out_or = stage2_out[1];
assign out_xor = stage2_out[2];

endmodule

module top_module( 
    input [3:0] in,
    output out_and,
    output out_or,
    output out_xor
);

pipelined_circuit pc(
    .in(in),
    .out_and(out_and),
    .out_or(out_or),
    .out_xor(out_xor)
);

endmodule