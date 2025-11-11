
module top_module(
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo,
    output wire [15:0] final_out
);

wire [15:0] mux_out;
wire [7:0] sel;

// Combinational Circuit from Problem 2
comb_circuit cc (
    .in(in),
    .out_hi(out_hi),
    .out_lo(out_lo)
);

// 256-to-1 Multiplexer from Problem 1
mux_256to1 mux (
    .in(in),
    .sel(sel),
    .out(mux_out)
);

// Additional Functional Module
adder add (
    .in1(out_hi),
    .in2(out_lo),
    .out(final_out)
);

endmodule
module comb_circuit (
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo
);
    assign out_hi = in[15:8];
    assign out_lo = in[7:0];
endmodule
module mux_256to1 (
    input wire [15:0] in,
    input wire [7:0] sel,
    output wire [15:0] out
);
    assign out = in << (sel * 8);
endmodule
module adder (
    input wire [7:0] in1,
    input wire [7:0] in2,
    output wire [15:0] out
);
    assign out = in1 + in2;
endmodule