
module top_module(
    input [31:0] a,
    input [31:0] b,
    input sel,
    output [31:0] sum
);

wire [7:0] adder1_out;
wire [7:0] adder2_out;
wire [15:0] adder3_out;
wire [3:0] mux_out;

mux_3_4 mux_inst(
    .a(a[23]),
    .b(a[15]),
    .c(a[7]),
    .sel(sel),
    .y(mux_out)
);

add_8 adder1_inst(
    .a(a[7:0]),
    .b(b[7:0]),
    .sum(adder1_out)
);

add_8 adder2_inst(
    .a(a[15:8]),
    .b(b[15:8]),
    .sum(adder2_out)
);

add_16 adder3_inst(
    .a(a[31:16]),
    .b(b[31:16]),
    .sum(adder3_out)
);

assign sum = sel ? {mux_out, a[31:23]} + b : a + b;

endmodule

module mux_3_4(
    input a,
    input b,
    input c,
    input sel,
    output [3:0] y
);

assign y[0] = (~sel & ~a) & b;
assign y[1] = (~sel & a) & c;
assign y[2] = (sel & ~a) & b;
assign y[3] = (sel & a) & c;

endmodule

module add_8(
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum
);

assign sum = a + b;

endmodule

module add_16(
    input [15:0] a,
    input [15:0] b,
    output [15:0] sum
);

add_8 adder1_inst(
    .a(a[7:0]),
    .b(b[7:0]),
    .sum(sum[7:0])
);

add_8 adder2_inst(
    .a(a[15:8]),
    .b(b[15:8]),
    .sum(sum[15:8])
);

endmodule
