
module mux_16to1_sel4_7_1 #(
    parameter ID = 0,
    parameter NUM_STAGE = 1,
    parameter din1_WIDTH = 7,
    parameter din2_WIDTH = 7,
    parameter din3_WIDTH = 7,
    parameter din4_WIDTH = 7,
    parameter din5_WIDTH = 7,
    parameter din6_WIDTH = 7,
    parameter din7_WIDTH = 7,
    parameter din8_WIDTH = 7,
    parameter din9_WIDTH = 7,
    parameter din10_WIDTH = 7,
    parameter din11_WIDTH = 7,
    parameter din12_WIDTH = 7,
    parameter din13_WIDTH = 7,
    parameter din14_WIDTH = 7,
    parameter din15_WIDTH = 7,
    parameter din16_WIDTH = 7,
    parameter din17_WIDTH = 4,
    parameter dout_WIDTH = 7
)(
    input [din1_WIDTH-1:0] din1,
    input [din2_WIDTH-1:0] din2,
    input [din3_WIDTH-1:0] din3,
    input [din4_WIDTH-1:0] din4,
    input [din5_WIDTH-1:0] din5,
    input [din6_WIDTH-1:0] din6,
    input [din7_WIDTH-1:0] din7,
    input [din8_WIDTH-1:0] din8,
    input [din9_WIDTH-1:0] din9,
    input [din10_WIDTH-1:0] din10,
    input [din11_WIDTH-1:0] din11,
    input [din12_WIDTH-1:0] din12,
    input [din13_WIDTH-1:0] din13,
    input [din14_WIDTH-1:0] din14,
    input [din15_WIDTH-1:0] din15,
    input [din16_WIDTH-1:0] din16,
    input [din17_WIDTH-1:0] din17,
    input [3:0] sel,
    output [dout_WIDTH-1:0] dout
);

// Internal wires
wire [din1_WIDTH-1:0] mux_1_0, mux_1_1, mux_1_2, mux_1_3, mux_1_4, mux_1_5, mux_1_6, mux_1_7;
wire [din1_WIDTH-1:0] mux_2_0, mux_2_1, mux_2_2, mux_2_3;
wire [din1_WIDTH-1:0] mux_3_0, mux_3_1;
wire [din1_WIDTH-1:0] mux_4_0;

// Generate level 1 logic
assign mux_1_0 = (sel[0] == 0) ? din1 : din2;
assign mux_1_1 = (sel[0] == 0) ? din3 : din4;
assign mux_1_2 = (sel[0] == 0) ? din5 : din6;
assign mux_1_3 = (sel[0] == 0) ? din7 : din8;
assign mux_1_4 = (sel[0] == 0) ? din9 : din10;
assign mux_1_5 = (sel[0] == 0) ? din11 : din12;
assign mux_1_6 = (sel[0] == 0) ? din13 : din14;
assign mux_1_7 = (sel[0] == 0) ? din15 : din16;

// Generate level 2 logic
assign mux_2_0 = (sel[1] == 0) ? mux_1_0 : mux_1_1;
assign mux_2_1 = (sel[1] == 0) ? mux_1_2 : mux_1_3;
assign mux_2_2 = (sel[1] == 0) ? mux_1_4 : mux_1_5;
assign mux_2_3 = (sel[1] == 0) ? mux_1_6 : mux_1_7;

// Generate level 3 logic
assign mux_3_0 = (sel[2] == 0) ? mux_2_0 : mux_2_1;
assign mux_3_1 = (sel[2] == 0) ? mux_2_2 : mux_2_3;

// Generate level 4 logic
assign mux_4_0 = (sel[3] == 0) ? mux_3_0 : mux_3_1;

// Output logic
assign dout = mux_4_0;

endmodule