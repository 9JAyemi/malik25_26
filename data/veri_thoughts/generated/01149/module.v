

module feedforward_mux_4to1_sel2_32_1 #(
parameter
    ID                = 0,
    NUM_STAGE         = 1,
    din1_WIDTH       = 32,
    din2_WIDTH       = 32,
    din3_WIDTH       = 32,
    din4_WIDTH       = 32,
    din5_WIDTH         = 32,
    dout_WIDTH            = 32
)(
    input  [31 : 0]     din1,
    input  [31 : 0]     din2,
    input  [31 : 0]     din3,
    input  [31 : 0]     din4,
    input  [1 : 0]    din5,
    output [31 : 0]   dout);

wire [1 : 0]     sel;
wire [31 : 0]         mux_1_0;
wire [31 : 0]         mux_1_1;
wire [31 : 0]         mux_2_0;

assign sel = din5;

assign mux_1_0 = (sel[0] == 0)? din1 : din2;
assign mux_1_1 = (sel[0] == 0)? din3 : din4;

assign mux_2_0 = (sel[1] == 0)? mux_1_0 : mux_1_1;

assign dout = mux_2_0;

endmodule
