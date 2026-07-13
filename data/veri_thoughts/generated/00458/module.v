module mux4to1(
    input in0,
    input in1,
    input in2,
    input in3,
    input [1:0] sel,
    output out
);

wire w1, w2;

// First 2:1 MUX
mux2to1 mux1(
    .in0(in0),
    .in1(in1),
    .sel(sel[0]),
    .out(w1)
);

// Second 2:1 MUX
mux2to1 mux2(
    .in0(in2),
    .in1(in3),
    .sel(sel[0]),
    .out(w2)
);

// Final 2:1 MUX
mux2to1 mux3(
    .in0(w1),
    .in1(w2),
    .sel(sel[1]),
    .out(out)
);

endmodule

module mux2to1(
    input in0,
    input in1,
    input sel,
    output out
);

assign out = sel ? in1 : in0;

endmodule