module top_module (
    input wire clk,
    input wire reset,
    input wire [1023:0] in,
    input wire [2:0] sel,
    input wire [2:0] vec,
    output wire [3:0] out,
    output wire o2,
    output wire o1,
    output wire o0 );

    wire [3:0] mux_out;
    wire [3:0] shifter_out;

    // 256-to-1 Multiplexer
    mux_256to1 mux_inst (
        .in(in),
        .sel(sel),
        .out(mux_out)
    );

    // Barrel Shifter
    barrel_shifter bs_inst (
        .in(mux_out),
        .vec(vec),
        .out(shifter_out),
        .o0(o0),
        .o1(o1),
        .o2(o2)
    );

    // Functional Module
    function_module func_inst (
        .mux_out(mux_out),
        .shifter_out(shifter_out),
        .vec(vec),
        .out(out)
    );

endmodule

module mux_256to1 (
    input wire [1023:0] in,
    input wire [2:0] sel,
    output wire [3:0] out );

    assign out = in[sel*4 +: 4];

endmodule

module barrel_shifter (
    input wire [3:0] in,
    input wire [2:0] vec,
    output wire [3:0] out,
    output wire o0,
    output wire o1,
    output wire o2 );

    wire [3:0] shift_1, shift_2, shift_3;

    assign shift_1 = {in[2:0], 1'b0};
    assign shift_2 = {in[1:0], 2'b00};
    assign shift_3 = {1'b0, in[0], 2'b00};

    assign out = (vec == 3'b000) ? in :
                 (vec == 3'b001) ? shift_1 :
                 (vec == 3'b010) ? shift_2 :
                 (vec == 3'b011) ? shift_3 :
                 4'b0000;

    assign o0 = in[0];
    assign o1 = in[1];
    assign o2 = in[2];

endmodule

module function_module (
    input wire [3:0] mux_out,
    input wire [3:0] shifter_out,
    input wire [2:0] vec,
    output wire [3:0] out );

    assign out = (vec == 3'b000) ? mux_out : shifter_out;

endmodule