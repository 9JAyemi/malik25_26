module top_module( 
    input [3:0] in,
    output out_add,
    output out_sub,
    output out_mul
);

wire [3:0] add_wire;
wire [3:0] sub_wire;
wire [7:0] mul_wire;

assign out_add = add_wire[0];
assign out_sub = sub_wire[0];
assign out_mul = mul_wire[0];

add_sub_module add_sub_inst(
    .in(in),
    .add_out(add_wire),
    .sub_out(sub_wire)
);

mul_module mul_inst(
    .in(in),
    .out(mul_wire)
);

endmodule

module add_sub_module(
    input [3:0] in,
    output [3:0] add_out,
    output [3:0] sub_out
);

assign add_out = in + 4'b0001;
assign sub_out = in - 4'b0001;

endmodule

module mul_module(
    input [3:0] in,
    output [7:0] out
);

assign out = in * in;

endmodule