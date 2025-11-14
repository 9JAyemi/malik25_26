
module adder (
    input [3:0] a,
    input [3:0] b,
    input cin,
    output [3:0] sum,
    output cout
);

wire [3:0] xor1_out, xor2_out, xor3_out, and1_out, and2_out, and3_out, and4_out, and5_out, and6_out;
wire [3:0] mux1_out, mux2_out, mux3_out;

// XOR gates
assign xor1_out[0] = a[0] ^ b[0];
assign xor1_out[1] = a[1] ^ b[1];
assign xor1_out[2] = a[2] ^ b[2];
assign xor1_out[3] = a[3] ^ b[3];

assign xor2_out[0] = cin ^ b[0];
assign xor2_out[1] = cin ^ b[1];
assign xor2_out[2] = cin ^ b[2];
assign xor2_out[3] = cin ^ b[3];

assign xor3_out[0] = cin ^ a[0];
assign xor3_out[1] = cin ^ a[1];
assign xor3_out[2] = cin ^ a[2];
assign xor3_out[3] = cin ^ a[3];

// AND gates
assign and1_out[0] = a[0] & b[0];
assign and1_out[1] = a[1] & b[1];
assign and1_out[2] = a[2] & b[2];
assign and1_out[3] = a[3] & b[3];

assign and2_out[0] = xor1_out[0] & cin;
assign and2_out[1] = xor1_out[1] & xor2_out[0];
assign and2_out[2] = xor1_out[2] & xor2_out[1];
assign and2_out[3] = xor1_out[3] & xor2_out[2];

assign and3_out[0] = xor1_out[0] & xor2_out[0];
assign and3_out[1] = xor1_out[1] & xor2_out[1];
assign and3_out[2] = xor1_out[2] & xor2_out[2];
assign and3_out[3] = xor1_out[3] & xor2_out[3];

assign and4_out[0] = xor1_out[0] & xor2_out[0] & cin;
assign and4_out[1] = xor1_out[1] & xor2_out[1] & xor3_out[0];
assign and4_out[2] = xor1_out[2] & xor2_out[2] & xor3_out[1];
assign and4_out[3] = xor1_out[3] & xor2_out[3] & xor3_out[2];

assign and5_out[0] = xor1_out[0] & xor2_out[0] & xor3_out[0];
assign and5_out[1] = xor1_out[1] & xor2_out[1] & xor3_out[1];
assign and5_out[2] = xor1_out[2] & xor2_out[2] & xor3_out[2];
assign and5_out[3] = and4_out[2];

assign and6_out[0] = xor1_out[0] & xor2_out[0] & xor3_out[0] & cin;
assign and6_out[1] = xor1_out[1] & xor2_out[1] & xor3_out[1] & xor2_out[0];
assign and6_out[2] = xor1_out[2] & xor2_out[2] & xor3_out[2] & xor2_out[1];
assign and6_out[3] = and4_out[3];

// 2-input multiplexers
mux2to1 #(4) mux1 (
    .a(xor1_out),
    .b(and2_out),
    .s(cin),
    .y(mux1_out)
);

mux2to1 #(4) mux2 (
    .a(xor2_out),
    .b(and3_out),
    .s(cin),
    .y(mux2_out)
);

mux2to1 #(4) mux3 (
    .a(xor3_out),
    .b(and4_out),
    .s(cin),
    .y(mux3_out)
);

// final sum
assign sum[0] = mux1_out[0];
assign sum[1] = mux2_out[1];
assign sum[2] = mux3_out[2];
assign sum[3] = and5_out[3];

// carry-out
assign cout = and6_out[3];

endmodule
module mux2to1 #(parameter WIDTH = 8) (
    input [WIDTH-1:0] a,
    input [WIDTH-1:0] b,
    input s,
    output [WIDTH-1:0] y
);

assign y = s ? b : a;

endmodule