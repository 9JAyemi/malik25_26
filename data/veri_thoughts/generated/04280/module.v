
module mux4_to_1_async_reset (
    input [3:0] in0,
    input [3:0] in1,
    input [3:0] in2,
    input [3:0] in3,
    input [1:0] sel,
    input reset,
    output [3:0] out
);

    wire [3:0] mux1_out;
    wire [3:0] mux2_out;
    wire [3:0] mux3_out;
    wire [3:0] mux4_out;

    // First stage of the mux
    mux4to1 mux1 (
        .in0(in0),
        .in1(in1),
        .in2(in2),
        .in3(in3),
        .sel(sel[1]),
        .out(mux1_out)
    );

    // Second stage of the mux
    mux4to1 mux2 (
        .in0(in0),
        .in1(in1),
        .in2(in2),
        .in3(in3),
        .sel(sel[0]),
        .out(mux2_out)
    );

    // Third stage of the mux
    mux2to1 mux3 (
        .in0(mux1_out),
        .in1(mux2_out),
        .sel(sel[1]),
        .out(mux3_out)
    );

    // Fourth stage of the mux
    mux2to1 mux4 (
        .in0(mux3_out),
        .in1(4'b0),
        .sel(reset),
        .out(mux4_out)
    );

    assign out = mux4_out;

endmodule
module mux4to1 (
    input [3:0] in0,
    input [3:0] in1,
    input [3:0] in2,
    input [3:0] in3,
    input sel,
    output [3:0] out
);

    wire [3:0] mux1_out;
    wire [3:0] mux2_out;

    // First stage of the mux
    mux2to1 mux1 (
        .in0(in0),
        .in1(in1),
        .sel(sel),
        .out(mux1_out)
    );

    // Second stage of the mux
    mux2to1 mux2 (
        .in0(in2),
        .in1(in3),
        .sel(sel),
        .out(mux2_out)
    );

    // Third stage of the mux
    mux2to1 mux3 (
        .in0(mux1_out),
        .in1(mux2_out),
        .sel(sel),
        .out(out)
    );

endmodule
module mux2to1 (
    input [3:0] in0,
    input [3:0] in1,
    input sel,
    output [3:0] out
);

    assign out = sel ? in1 : in0;

endmodule