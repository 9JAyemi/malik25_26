
module decoder_4to16 (
    input [3:0] in, // Input to the decoder
    output [15:0] out // Output from the decoder
);

// Internal wires
wire [15:0] temp;

// Decoder logic
assign temp[0] = ~in[3] & ~in[2] & ~in[1] & ~in[0];
assign temp[1] = ~in[3] & ~in[2] & ~in[1] & in[0];
assign temp[2] = ~in[3] & ~in[2] & in[1] & ~in[0];
assign temp[3] = ~in[3] & ~in[2] & in[1] & in[0];
assign temp[4] = ~in[3] & in[2] & ~in[1] & ~in[0];
assign temp[5] = ~in[3] & in[2] & ~in[1] & in[0];
assign temp[6] = ~in[3] & in[2] & in[1] & ~in[0];
assign temp[7] = ~in[3] & in[2] & in[1] & in[0];
assign temp[8] = in[3] & ~in[2] & ~in[1] & ~in[0];
assign temp[9] = in[3] & ~in[2] & ~in[1] & in[0];
assign temp[10] = in[3] & ~in[2] & in[1] & ~in[0];
assign temp[11] = in[3] & ~in[2] & in[1] & in[0];
assign temp[12] = in[3] & in[2] & ~in[1] & ~in[0];
assign temp[13] = in[3] & in[2] & ~in[1] & in[0];
assign temp[14] = in[3] & in[2] & in[1] & ~in[0];
assign temp[15] = in[3] & in[2] & in[1] & in[0];

// Output logic
assign out = temp;

endmodule
