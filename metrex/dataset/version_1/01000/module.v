module splitter (
    input wire [2:0] in,
    output wire o2,
    output wire o1,
    output wire o0
);
    assign {o2, o1, o0} = in;
endmodule

module barrel_shifter (
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo
);
    assign {out_hi, out_lo} = in >> 8;
endmodule

module top_module (
    input wire [18:0] in,
    input wire select,
    output wire [18:0] out,
    output wire o2,
    output wire o1,
    output wire o0,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo
);
    wire [2:0] splitter_out;
    wire [7:0] barrel_out_hi;
    wire [7:0] barrel_out_lo;

    splitter splitter_inst (
        .in(in[2:0]),
        .o2(o2),
        .o1(o1),
        .o0(o0)
    );

    barrel_shifter barrel_inst (
        .in(in[18:3]),
        .out_hi(barrel_out_hi),
        .out_lo(barrel_out_lo)
    );

    assign out = select ? {barrel_out_hi, {splitter_out, barrel_out_lo}} : {barrel_out_hi, barrel_out_lo};
    assign splitter_out = {o2, o1, o0};
    assign out_hi = barrel_out_hi;
    assign out_lo = select ? {splitter_out, barrel_out_lo} : barrel_out_lo;
endmodule