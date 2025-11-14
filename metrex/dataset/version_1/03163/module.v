
module mux4to1(
    input [3:0] in0,
    input [3:0] in1,
    input [3:0] in2,
    input [3:0] in3,
    input [1:0] sel,
    output [3:0] out
);

    wire [3:0] mux1_out0, mux1_out1;

    // First level MUXes
    mux2to1 mux1_0(
        .in0(in0),
        .in1(in1),
        .sel(sel[0]),
        .out(mux1_out0)
    );
    mux2to1 mux1_1(
        .in0(in2),
        .in1(in3),
        .sel(sel[0]),
        .out(mux1_out1)
    );

    // Second level MUX
    mux2to1 mux2(
        .in0(mux1_out0),
        .in1(mux1_out1),
        .sel(sel[1]),
        .out(out)
    );

endmodule

module mux2to1(
    input [3:0] in0,
    input [3:0] in1,
    input sel,
    output [3:0] out
);

    assign out = sel ? in1 : in0;

endmodule
