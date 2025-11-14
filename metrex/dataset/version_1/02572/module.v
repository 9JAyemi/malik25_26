module and_or_xnor_vector (
    input clk,
    input reset,      // Synchronous active-high reset
    input [3:0] in,   // 4-bit input vector
    input select,     // Select input to choose between AND/OR/XNOR gate and input vector splitter
    output out_and,   // Output of the 4-input AND gate
    output out_or,    // Output of the 4-input OR gate
    output out_xnor,  // Output of the 4-input XNOR gate
    output [2:0] outv // 3-bit vector that represents the input vector's positions 0, 1, and 2, respectively
);

wire [2:0] in_split;
wire [3:0] and_or_xnor_in;

and_or_xnor and_or_xnor_inst (
    .in(and_or_xnor_in),
    .out_and(out_and),
    .out_or(out_or),
    .out_xnor(out_xnor)
);

input_vector_splitter input_vector_splitter_inst (
    .in(in),
    .out(in_split)
);

assign and_or_xnor_in = select ? {in_split[2], in_split[1], in_split[0], in_split[0]} : {in[3], in[2], in[1], in[0]};

assign outv[0] = in[0] & in[1] & in[2];
assign outv[1] = ~in[0] & ~in[1] & ~in[2];
assign outv[2] = {in[2], in[1], in[0]};

endmodule

module and_or_xnor (
    input [3:0] in,
    output out_and,
    output out_or,
    output out_xnor
);

assign out_and = in[0] & in[1] & in[2] & in[3];
assign out_or = in[0] | in[1] | in[2] | in[3];
assign out_xnor = ~(in[0] ^ in[1] ^ in[2] ^ in[3]);

endmodule

module input_vector_splitter (
    input [3:0] in,
    output [2:0] out
);

assign out[0] = in[0];
assign out[1] = in[1];
assign out[2] = in[2];

endmodule