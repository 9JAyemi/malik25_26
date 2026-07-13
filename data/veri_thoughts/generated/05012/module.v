
module top_module (
    input CLK, RESET, // Synchronous active-high reset
    input [2:0] in, // Input to the decoder
    input enable, // Enable input to the decoder
    input SHIFT_LEFT, SHIFT_RIGHT, // Control inputs to the barrel shifter
    input [3:0] DATA, // Input to the barrel shifter
    output [7:0] out // Output from the functional module
);

// Decoder module
wire [7:0] out_decoder;
decoder dec(
    .in(in),
    .enable(enable),
    .out(out_decoder)
);

// Barrel shifter module
wire [3:0] out_shifter;
barrel_shifter shifter(
    .in(DATA),
    .shift_left(SHIFT_LEFT),
    .shift_right(SHIFT_RIGHT),
    .out(out_shifter)
);

// Functional module
assign out = out_decoder | out_shifter;

endmodule
module decoder (
    input [2:0] in,
    input enable,
    output [7:0] out
);

assign out = (enable) ? (1 << in) : 8'b0;

endmodule
module barrel_shifter (
    input [3:0] in,
    input shift_left,
    input shift_right,
    output [3:0] out
);

assign out = (shift_left) ? ({in[2:0], 1'b0}) :
             (shift_right) ? ({1'b0, in[3:1]}) :
             in;

endmodule