module barrel_shifter (
    input wire [15:0] in,
    output wire [7:0] out
);

assign out = in[7:0];

endmodule

module mux_2to1 (
    input wire [7:0] in0,
    input wire [7:0] in1,
    input wire ctrl,
    output wire [7:0] out
);

assign out = ctrl ? in1 : in0;

endmodule

module bitwise_or (
    input wire [7:0] in0,
    input wire [7:0] in1,
    output wire [7:0] out
);

assign out = in0 | in1;

endmodule

module top_module (
    input wire [15:0] in,
    input ctrl,
    output wire [7:0] out,
    output wire [7:0] out_or
);

wire [7:0] upper_out;
wire [7:0] lower_out;

barrel_shifter bs(in, lower_out);
barrel_shifter bs_upper(in >> 8, upper_out);

mux_2to1 mux(lower_out, upper_out, ctrl, out);
bitwise_or or_gate(lower_out, upper_out, out_or);

endmodule