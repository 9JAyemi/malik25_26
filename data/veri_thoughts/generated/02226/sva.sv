module mux_16to1_sel4_7_1_sva #(
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
) (
    input logic clk,
    input logic [din1_WIDTH-1:0]  din1,
    input logic [din2_WIDTH-1:0]  din2,
    input logic [din3_WIDTH-1:0]  din3,
    input logic [din4_WIDTH-1:0]  din4,
    input logic [din5_WIDTH-1:0]  din5,
    input logic [din6_WIDTH-1:0]  din6,
    input logic [din7_WIDTH-1:0]  din7,
    input logic [din8_WIDTH-1:0]  din8,
    input logic [din9_WIDTH-1:0]  din9,
    input logic [din10_WIDTH-1:0] din10,
    input logic [din11_WIDTH-1:0] din11,
    input logic [din12_WIDTH-1:0] din12,
    input logic [din13_WIDTH-1:0] din13,
    input logic [din14_WIDTH-1:0] din14,
    input logic [din15_WIDTH-1:0] din15,
    input logic [din16_WIDTH-1:0] din16,
    input logic [din17_WIDTH-1:0] din17, // unused in RTL
    input logic [3:0] sel,
    input logic [dout_WIDTH-1:0] dout
);

    ///// 16:1 mux mapping from sel to dout /////
    // When sel==0, dout equals din1.
    route_sel0_to_din1: assert property (
        @(posedge clk) (sel == 4'd0) |-> (dout == din1)
    );
    // When sel==1, dout equals din2.
    route_sel1_to_din2: assert property (
        @(posedge clk) (sel == 4'd1) |-> (dout == din2)
    );
    // When sel==2, dout equals din3.
    route_sel2_to_din3: assert property (
        @(posedge clk) (sel == 4'd2) |-> (dout == din3)
    );
    // When sel==3, dout equals din4.
    route_sel3_to_din4: assert property (
        @(posedge clk) (sel == 4'd3) |-> (dout == din4)
    );
    // When sel==4, dout equals din5.
    route_sel4_to_din5: assert property (
        @(posedge clk) (sel == 4'd4) |-> (dout == din5)
    );
    // When sel==5, dout equals din6.
    route_sel5_to_din6: assert property (
        @(posedge clk) (sel == 4'd5) |-> (dout == din6)
    );
    // When sel==6, dout equals din7.
    route_sel6_to_din7: assert property (
        @(posedge clk) (sel == 4'd6) |-> (dout == din7)
    );
    // When sel==7, dout equals din8.
    route_sel7_to_din8: assert property (
        @(posedge clk) (sel == 4'd7) |-> (dout == din8)
    );
    // When sel==8, dout equals din9.
    route_sel8_to_din9: assert property (
        @(posedge clk) (sel == 4'd8) |-> (dout == din9)
    );
    // When sel==9, dout equals din10.
    route_sel9_to_din10: assert property (
        @(posedge clk) (sel == 4'd9) |-> (dout == din10)
    );
    // When sel==10, dout equals din11.
    route_sel10_to_din11: assert property (
        @(posedge clk) (sel == 4'd10) |-> (dout == din11)
    );
    // When sel==11, dout equals din12.
    route_sel11_to_din12: assert property (
        @(posedge clk) (sel == 4'd11) |-> (dout == din12)
    );
    // When sel==12, dout equals din13.
    route_sel12_to_din13: assert property (
        @(posedge clk) (sel == 4'd12) |-> (dout == din13)
    );
    // When sel==13, dout equals din14.
    route_sel13_to_din14: assert property (
        @(posedge clk) (sel == 4'd13) |-> (dout == din14)
    );
    // When sel==14, dout equals din15.
    route_sel14_to_din15: assert property (
        @(posedge clk) (sel == 4'd14) |-> (dout == din15)
    );
    // When sel==15, dout equals din16.
    route_sel15_to_din16: assert property (
        @(posedge clk) (sel == 4'd15) |-> (dout == din16)
    );

endmodule