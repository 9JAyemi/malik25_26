
module top_module (
    input wire [15:0] in,
    input wire [2:0] sel,
    input wire [3:0] data0,
    input wire [3:0] data1,
    input wire [3:0] data2,
    input wire [3:0] data3,
    input wire [3:0] data4,
    input wire [3:0] data5,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo
);

    wire [3:0] mux_out;
    wire [7:0] split_out_hi;
    wire [7:0] split_out_lo;
    wire [7:0] and_out;

    assign mux_out = (sel == 0) ? data0 :
                     (sel == 1) ? data1 :
                     (sel == 2) ? data2 :
                     (sel == 3) ? data3 :
                     (sel == 4) ? data4 : data5;
    assign split_out_hi = in[15:8];
    assign split_out_lo = in[7:0];
    assign and_out = split_out_hi & split_out_lo;

    assign out_lo = and_out;
    assign out_hi = mux_out;

endmodule