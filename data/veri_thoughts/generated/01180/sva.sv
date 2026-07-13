module sp_mux_16to1_sel4_7_1_sva (
    input logic clk,
    input  [6:0] din1,
    input  [6:0] din2,
    input  [6:0] din3,
    input  [6:0] din4,
    input  [6:0] din5,
    input  [6:0] din6,
    input  [6:0] din7,
    input  [6:0] din8,
    input  [6:0] din9,
    input  [6:0] din10,
    input  [6:0] din11,
    input  [6:0] din12,
    input  [6:0] din13,
    input  [6:0] din14,
    input  [6:0] din15,
    input  [6:0] din16,
    input  [3:0] din17,
    input  [6:0] dout
);
    // sel==0 selects din1
    check_sel_0_maps_to_din1: assert property (
        @(posedge clk) (din17 == 4'd0) |-> (dout == din1)
    );
    // sel==1 selects din2
    check_sel_1_maps_to_din2: assert property (
        @(posedge clk) (din17 == 4'd1) |-> (dout == din2)
    );
    // sel==2 selects din3
    check_sel_2_maps_to_din3: assert property (
        @(posedge clk) (din17 == 4'd2) |-> (dout == din3)
    );
    // sel==3 selects din4
    check_sel_3_maps_to_din4: assert property (
        @(posedge clk) (din17 == 4'd3) |-> (dout == din4)
    );
    // sel==4 selects din5
    check_sel_4_maps_to_din5: assert property (
        @(posedge clk) (din17 == 4'd4) |-> (dout == din5)
    );
    // sel==5 selects din6
    check_sel_5_maps_to_din6: assert property (
        @(posedge clk) (din17 == 4'd5) |-> (dout == din6)
    );
    // sel==6 selects din7
    check_sel_6_maps_to_din7: assert property (
        @(posedge clk) (din17 == 4'd6) |-> (dout == din7)
    );
    // sel==7 selects din8
    check_sel_7_maps_to_din8: assert property (
        @(posedge clk) (din17 == 4'd7) |-> (dout == din8)
    );
    // sel==8 selects din9
    check_sel_8_maps_to_din9: assert property (
        @(posedge clk) (din17 == 4'd8) |-> (dout == din9)
    );
    // sel==9 selects din10
    check_sel_9_maps_to_din10: assert property (
        @(posedge clk) (din17 == 4'd9) |-> (dout == din10)
    );
    // sel==10 selects din11
    check_sel_10_maps_to_din11: assert property (
        @(posedge clk) (din17 == 4'd10) |-> (dout == din11)
    );
    // sel==11 selects din12
    check_sel_11_maps_to_din12: assert property (
        @(posedge clk) (din17 == 4'd11) |-> (dout == din12)
    );
    // sel==12 selects din13
    check_sel_12_maps_to_din13: assert property (
        @(posedge clk) (din17 == 4'd12) |-> (dout == din13)
    );
    // sel==13 selects din14
    check_sel_13_maps_to_din14: assert property (
        @(posedge clk) (din17 == 4'd13) |-> (dout == din14)
    );
    // sel==14 selects din15
    check_sel_14_maps_to_din15: assert property (
        @(posedge clk) (din17 == 4'd14) |-> (dout == din15)
    );
    // sel==15 selects din16
    check_sel_15_maps_to_din16: assert property (
        @(posedge clk) (din17 == 4'd15) |-> (dout == din16)
    );
endmodule