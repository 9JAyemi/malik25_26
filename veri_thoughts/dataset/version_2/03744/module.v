

module sp_mux_6to1_sel3_7_1 #(
parameter
    ID                = 0,
    NUM_STAGE         = 1,
    din1_WIDTH       = 32,
    din2_WIDTH       = 32,
    din3_WIDTH       = 32,
    din4_WIDTH       = 32,
    din5_WIDTH       = 32,
    din6_WIDTH       = 32,
    din7_WIDTH         = 32,
    dout_WIDTH            = 32
)(
    input  [6 : 0]     din1,
    input  [6 : 0]     din2,
    input  [6 : 0]     din3,
    input  [6 : 0]     din4,
    input  [6 : 0]     din5,
    input  [6 : 0]     din6,
    input  [2 : 0]    din7,
    output [6 : 0]   dout);

wire [2 : 0]     sel;
wire [6 : 0]         mux_1_0;
wire [6 : 0]         mux_1_1;
wire [6 : 0]         mux_1_2;
wire [6 : 0]         mux_2_0;
wire [6 : 0]         mux_2_1;
wire [6 : 0]         mux_3_0;

assign sel = din7;

assign mux_1_0 = (sel[0] == 0)? din1 : din2;
assign mux_1_1 = (sel[0] == 0)? din3 : din4;
assign mux_1_2 = (sel[0] == 0)? din5 : din6;

assign mux_2_0 = (sel[1] == 0)? mux_1_0 : mux_1_1;
assign mux_2_1 = mux_1_2;

assign mux_3_0 = (sel[2] == 0)? mux_2_0 : mux_2_1;

assign dout = mux_3_0;

endmodule
