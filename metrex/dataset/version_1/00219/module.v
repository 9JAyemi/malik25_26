
module top_module (
    input [3:0] a,
    input [3:0] b,
    input [3:0] c,
    input [3:0] d,
    input [1:0] sel,
    output [3:0] out_mux
);

wire [3:0] mux1_out;
wire [3:0] mux2_out;

// 2-to-1 multiplexer instances
mux2to1 mux1({a[3], a[2], a[1], a[0]}, {b[3], b[2], b[1], b[0]}, sel[0], mux1_out);
mux2to1 mux2({c[3], c[2], c[1], c[0]}, {d[3], d[2], d[1], d[0]}, sel[0], mux2_out);


// 2-to-1 multiplexer for final output
mux2to1 mux3(mux1_out, mux2_out, sel[1], out_mux);

endmodule

module mux2to1 (
    input [3:0] a,
    input [3:0] b,
    input sel,
    output [3:0] out
);

assign out = sel ? b : a;

endmodule
