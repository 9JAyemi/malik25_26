
module top_module(
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo );

    wire [7:0] sum_hi;
    wire [7:0] sum_lo;

    byte_decoder decoder(.in(in), .out_hi(sum_hi), .out_lo(sum_lo));
    byte_mux mux_hi(.a(sum_hi), .b(8'b0), .sel(in[15]), .out(out_hi));
    byte_mux mux_lo(.a(sum_lo), .b(8'b0), .sel(in[7]), .out(out_lo));

endmodule
module byte_decoder(
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo );

    assign out_hi = in[15:8];
    assign out_lo = in[7:0];

endmodule
module byte_mux(
    input wire [7:0] a,
    input wire [7:0] b,
    input wire sel,
    output wire [7:0] out );

    assign out = sel ? b : a;

endmodule