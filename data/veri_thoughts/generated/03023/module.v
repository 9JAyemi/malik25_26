module top_module( 
    input [99:0] in,
    output out_and,
    output out_or,
    output out_xor 
);

wire [9:0] and_out;
wire [9:0] or_out;
wire [9:0] xor_out;

assign out_and = and_out[9];
assign out_or = or_out[9];
assign out_xor = xor_out[9];

and_gate and0(.in(in[9:0]), .out(and_out[0]));
and_gate and1(.in(in[19:10]), .out(and_out[1]));
and_gate and2(.in(in[29:20]), .out(and_out[2]));
and_gate and3(.in(in[39:30]), .out(and_out[3]));
and_gate and4(.in(in[49:40]), .out(and_out[4]));
and_gate and5(.in(in[59:50]), .out(and_out[5]));
and_gate and6(.in(in[69:60]), .out(and_out[6]));
and_gate and7(.in(in[79:70]), .out(and_out[7]));
and_gate and8(.in(in[89:80]), .out(and_out[8]));
and_gate and9(.in(in[99:90]), .out(and_out[9]));

or_gate or0(.in(in[9:0]), .out(or_out[0]));
or_gate or1(.in(in[19:10]), .out(or_out[1]));
or_gate or2(.in(in[29:20]), .out(or_out[2]));
or_gate or3(.in(in[39:30]), .out(or_out[3]));
or_gate or4(.in(in[49:40]), .out(or_out[4]));
or_gate or5(.in(in[59:50]), .out(or_out[5]));
or_gate or6(.in(in[69:60]), .out(or_out[6]));
or_gate or7(.in(in[79:70]), .out(or_out[7]));
or_gate or8(.in(in[89:80]), .out(or_out[8]));
or_gate or9(.in(in[99:90]), .out(or_out[9]));

xor_gate xor0(.in(in[9:0]), .out(xor_out[0]));
xor_gate xor1(.in(in[19:10]), .out(xor_out[1]));
xor_gate xor2(.in(in[29:20]), .out(xor_out[2]));
xor_gate xor3(.in(in[39:30]), .out(xor_out[3]));
xor_gate xor4(.in(in[49:40]), .out(xor_out[4]));
xor_gate xor5(.in(in[59:50]), .out(xor_out[5]));
xor_gate xor6(.in(in[69:60]), .out(xor_out[6]));
xor_gate xor7(.in(in[79:70]), .out(xor_out[7]));
xor_gate xor8(.in(in[89:80]), .out(xor_out[8]));
xor_gate xor9(.in(in[99:90]), .out(xor_out[9]));

endmodule

module and_gate(
    input [9:0] in,
    output out
);

assign out = &in;

endmodule

module or_gate(
    input [9:0] in,
    output out
);

assign out = |in;

endmodule

module xor_gate(
    input [9:0] in,
    output out
);

assign out = ^in;

endmodule