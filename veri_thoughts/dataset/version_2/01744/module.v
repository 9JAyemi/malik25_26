

module sp_mux_5to1_sel3_4_1 #(
parameter
    ID                = 0,
    NUM_STAGE         = 1,
    din1_WIDTH       = 32,
    din2_WIDTH       = 32,
    din3_WIDTH       = 32,
    din4_WIDTH       = 32,
    din5_WIDTH       = 32,
    din6_WIDTH         = 32,
    dout_WIDTH            = 32
)(
    input  [3 : 0]     din1,
    input  [3 : 0]     din2,
    input  [3 : 0]     din3,
    input  [3 : 0]     din4,
    input  [3 : 0]     din5,
    input  [2 : 0]    din6,
    output [3 : 0]   dout);

wire [2 : 0]     sel;
wire [3 : 0]         mux_1_0;
wire [3 : 0]         mux_1_1;
wire [3 : 0]         mux_1_2;
wire [3 : 0]         mux_2_0;
wire [3 : 0]         mux_2_1;
wire [3 : 0]         mux_3_0;

assign sel = din6;

assign mux_1_0 = (sel[0] == 0)? din1 : din2;
assign mux_1_1 = (sel[0] == 0)? din3 : din4;
assign mux_1_2 = din5;

assign mux_2_0 = (sel[1] == 0)? mux_1_0 : mux_1_1;
assign mux_2_1 = mux_1_2;

assign mux_3_0 = (sel[2] == 0)? mux_2_0 : mux_2_1;

assign dout = mux_3_0;

endmodule
