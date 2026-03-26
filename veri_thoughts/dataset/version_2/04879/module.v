module byte_order_reverse (
    input [31:0] in,
    output [31:0] out
);
    assign out = {in[7:0], in[15:8], in[23:16], in[31:24]};
endmodule

module mux_6to1 (
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    output [3:0] out
);
    reg [3:0] mux_out;
    always @*
        case (sel)
            3'b000: mux_out = data0;
            3'b001: mux_out = data1;
            3'b010: mux_out = data2;
            3'b011: mux_out = data3;
            3'b100: mux_out = data4;
            3'b101: mux_out = data5;
            default: mux_out = 4'b0000;
        endcase
    assign out = mux_out;
endmodule

module sum_module (
    input [31:0] byte_order_rev_out,
    input [3:0] mux_out,
    output [31:0] sum_out
);
    assign sum_out = byte_order_rev_out + {28'b0, mux_out};
endmodule

module top_module (
    input [31:0] in,
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    output [3:0] out
);
    wire [31:0] byte_order_rev_out;
    wire [3:0] mux_out;
    wire [31:0] sum_out;

    byte_order_reverse byte_order_rev(in, byte_order_rev_out);
    mux_6to1 mux(sel, data0, data1, data2, data3, data4, data5, mux_out);
    sum_module sum(byte_order_rev_out, mux_out, sum_out);

    assign out = sum_out[3:0];
endmodule