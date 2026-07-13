

module hls_saturation_enqcK #(
parameter
    ID                = 0,
    NUM_STAGE         = 1,
    din0_WIDTH       = 32,
    din1_WIDTH       = 32,
    din2_WIDTH       = 32,
    din3_WIDTH       = 32,
    din4_WIDTH         = 32,
    dout_WIDTH            = 32
)(
    input  [27 : 0]     din0,
    input  [27 : 0]     din1,
    input  [27 : 0]     din2,
    input  [27 : 0]     din3,
    input  [1 : 0]    din4,
    output [27 : 0]   dout);

wire [1 : 0]     sel;
wire [27 : 0]         mux_1_0;
wire [27 : 0]         mux_1_1;
wire [27 : 0]         mux_2_0;

assign sel = din4;

assign mux_1_0 = (sel[0] == 0)? din0 : din1;
assign mux_1_1 = (sel[0] == 0)? din2 : din3;

assign mux_2_0 = (sel[1] == 0)? mux_1_0 : mux_1_1;

assign dout = mux_2_0;

endmodule
