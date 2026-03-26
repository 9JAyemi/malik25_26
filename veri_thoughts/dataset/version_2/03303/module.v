
module mux_6to1 (
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    output [3:0] out
);

reg [3:0] out_reg;

always @(*) begin
    case (sel)
        3'b000: out_reg = data0;
        3'b001: out_reg = data1;
        3'b010: out_reg = data2;
        3'b011: out_reg = data3;
        default: out_reg = 4'b0000;
    endcase
end

assign out = out_reg;

endmodule
module priority_encoder_min (
    input [7:0] a,
    input [7:0] b,
    input [7:0] c,
    input [7:0] d,
    output [1:0] out
);

wire [3:0] min_index;

assign min_index = (a <= b && a <= c && a <= d) ? 2'b00 :
                  (b <= c && b <= d) ? 2'b01 :
                  (c <= d) ? 2'b10 : 2'b11;

assign out = min_index;

endmodule
module top_module (
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [7:0] a,
    input [7:0] b,
    input [7:0] c,
    input [7:0] d,
    output [7:0] sum
);

wire [3:0] mux_out;
wire [1:0] min_index;

mux_6to1 mux_inst (
    .sel(sel),
    .data0(data0),
    .data1(data1),
    .data2(data2),
    .data3(data3),
    .out(mux_out)
);

priority_encoder_min priority_inst (
    .a(a),
    .b(b),
    .c(c),
    .d(d),
    .out(min_index)
);

assign sum = mux_out + min_index;

endmodule