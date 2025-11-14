
module mux_parity (
    input [7:0] a, // 8-bit input a
    input [7:0] b, // 8-bit input b
    input sel_b1, // Select input 1 for 2-to-1 MUX
    input sel_b2, // Select input 2 for 2-to-1 MUX
    output [8:0] out // 9-bit output with parity bit added as MSB
);

wire [7:0] mux_out;
wire parity;

mux_2to1 mux_inst (
    .in0(a),
    .in1(b),
    .sel(sel_b1),
    .out(mux_out)
);

parity_generator parity_inst (
    .in(mux_out),
    .out(parity)
);

// Connect the parity signal to the output
assign out = {parity, mux_out};

endmodule

module mux_2to1 (
    input [7:0] in0, // Input 0
    input [7:0] in1, // Input 1
    input sel, // Select input
    output [7:0] out // Output
);

assign out = sel ? in1 : in0;

endmodule

module parity_generator (
    input [7:0] in, // Input byte
    output out // Parity bit
);

assign out = in[0] ^ in[1] ^ in[2] ^ in[3] ^ in[4] ^ in[5] ^ in[6] ^ in[7];

endmodule
