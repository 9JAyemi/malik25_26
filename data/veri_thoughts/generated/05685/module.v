module mux_or (
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input select,
    output [3:0] out
);

    wire [3:0] mux_out1, mux_out2;

    // First 2-to-1 Mux
    mux2to1 mux1 (
        .in0(data0),
        .in1(data1),
        .sel(select),
        .out(mux_out1)
    );

    // Second 2-to-1 Mux
    mux2to1 mux2 (
        .in0(data2),
        .in1(data3),
        .sel(select),
        .out(mux_out2)
    );

    // Bitwise OR functional module
    or4 or_module (
        .in0(mux_out1),
        .in1(mux_out2),
        .out(out)
    );

endmodule

// 2-to-1 Mux module
module mux2to1 (
    input [3:0] in0,
    input [3:0] in1,
    input sel,
    output [3:0] out
);

    assign out = sel ? in1 : in0;

endmodule

// Bitwise OR functional module
module or4 (
    input [3:0] in0,
    input [3:0] in1,
    output [3:0] out
);

    assign out = in0 | in1;

endmodule