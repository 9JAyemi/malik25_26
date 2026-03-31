
module priority_encoder (
    input [7:0] a, b, c, d,
    output reg [1:0] out
);

always @* begin
    if (a > b && a > c && a > d) out = 2'b00;
    else if (b > c && b > d) out = 2'b01;
    else if (c > d) out = 2'b10;
    else out = 2'b11;
end

endmodule
module mux (
    input [7:0] a, b, c, d,
    input [1:0] sel,
    output reg [7:0] out
);

always @* begin
    case (sel)
        2'b00: out = a;
        2'b01: out = b;
        2'b10: out = c;
        2'b11: out = d;
    endcase
end

endmodule
module comb_logic (
    input [99:0] in,
    output wire out_and,
    output wire out_or,
    output wire out_xor
);

wire [49:0] and_wires;
wire [49:0] or_wires;
wire [49:0] xor_wires;

assign and_wires = {50{1'b1}} & in[49:0];
assign or_wires = {50{1'b0}} | in[49:0];
assign xor_wires = {50{1'b0}} ^ in[49:0];

assign out_and = &and_wires;
assign out_or = |or_wires;
assign out_xor = ^xor_wires;

endmodule
module top_module (
    input clk,
    input reset,
    input [99:0] in,
    input [7:0] a, b, c, d,
    output [7:0] min,
    output out
);

wire [1:0] priority_out;
wire [7:0] mux_out;
wire out_and, out_or, out_xor;

priority_encoder pe(.a(a), .b(b), .c(c), .d(d), .out(priority_out));
mux mux(.a(a), .b(b), .c(c), .d(d), .sel(priority_out), .out(mux_out));
comb_logic cl(.in(in), .out_and(out_and), .out_or(out_or), .out_xor(out_xor));
assign min = mux_out;
assign out = out_and | out_or | out_xor;

endmodule