
module top_module (
    input [15:0] in0,
    input [15:0] in1,
    input CTRL,
    input CLK,
    output [15:0] OUT_ADDSUB,
    output [15:0] OUT_DIFF
);

wire [15:0] add_out;
wire [15:0] sub_out;

adder adder_inst (
    .in0(in0),
    .in1(in1),
    .out(add_out)
);

subtractor sub_inst (
    .in0(in0),
    .in1(in1),
    .out(sub_out)
);

assign OUT_ADDSUB = CTRL ? sub_out : add_out;

absolute_diff diff_inst (
    .in0(add_out),
    .in1(sub_out),
    .out(OUT_DIFF)
);

endmodule
module adder (
    input [15:0] in0,
    input [15:0] in1,
    output [15:0] out
);

assign out = in0 + in1;

endmodule
module subtractor (
    input [15:0] in0,
    input [15:0] in1,
    output [15:0] out
);

assign out = in0 - in1;

endmodule
module absolute_diff (
    input [15:0] in0,
    input [15:0] in1,
    output [15:0] out
);

assign out = in0 > in1 ? in0 - in1 : in1 - in0;

endmodule