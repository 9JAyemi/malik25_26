module bcd_converter (
    input [3:0] in,
    output [3:0] bcd_high,
    output [3:0] bcd_low
);

wire [6:0] bcd_out;
assign bcd_out = (in >= 5) ? (3'd3 << 4) | (in - 5) : (3'd0 << 4) | in;

assign bcd_high = bcd_out[6:4];
assign bcd_low = bcd_out[3:0];

endmodule
module mux_and_adder (
    input [15:0] mux_in,
    input [3:0] sel,
    input EN,
    input [3:0] bcd_high,
    input [3:0] bcd_low,
    output reg [3:0] bcd_sum
);

always @(*) begin
    case (sel)
        4'b0000: bcd_sum = bcd_low + mux_in[3:0];
        4'b0001: bcd_sum = bcd_low + mux_in[7:4];
        4'b0010: bcd_sum = bcd_low + mux_in[11:8];
        4'b0011: bcd_sum = bcd_low + mux_in[15:12];
        4'b0100: bcd_sum = bcd_high + mux_in[3:0];
        4'b0101: bcd_sum = bcd_high + mux_in[7:4];
        4'b0110: bcd_sum = bcd_high + mux_in[11:8];
        4'b0111: bcd_sum = bcd_high + mux_in[15:12];
        4'b1000: bcd_sum = bcd_low + bcd_high + mux_in[3:0];
        4'b1001: bcd_sum = bcd_low + bcd_high + mux_in[7:4];
        4'b1010: bcd_sum = bcd_low + bcd_high + mux_in[11:8];
        4'b1011: bcd_sum = bcd_low + bcd_high + mux_in[15:12];
        default: bcd_sum = 4'b0000;
    endcase
end

endmodule
module top_module (
    input [3:0] in,
    input [15:0] mux_in,
    input [3:0] sel,
    input EN,
    output [3:0] bcd_high,
    output [3:0] bcd_low
);

wire [3:0] bcd_high_wire;
wire [3:0] bcd_low_wire;
wire [3:0] bcd_sum;

bcd_converter bcd_converter_inst (
    .in(in),
    .bcd_high(bcd_high_wire),
    .bcd_low(bcd_low_wire)
);

mux_and_adder mux_and_adder_inst (
    .mux_in(mux_in),
    .sel(sel),
    .EN(EN),
    .bcd_high(bcd_high_wire),
    .bcd_low(bcd_low_wire),
    .bcd_sum(bcd_sum)
);

bcd_converter bcd_converter_inst2 (
    .in(bcd_sum),
    .bcd_high(bcd_high),
    .bcd_low(bcd_low)
);

endmodule
