module Priority_Codec_32_sva (
    input logic        clk,
    input logic [25:0] Data_Dec_i,
    input logic [4:0]  Data_Bin_o
);

    // No clock or reset exists in the DUT; clk is an external sampling clock.
    // The DUT is combinational and selects the first low bit from [25] down to [0].

    // If bit 25 is low, the output maps to 0.
    check_bit25_low_maps_to_0: assert property (
        @(posedge clk) (~Data_Dec_i[25]) |-> (Data_Bin_o == 5'b00000)
    );

    // If bit 24 is the first low bit, the output maps to 1.
    check_bit24_first_low_maps_to_1: assert property (
        @(posedge clk) (Data_Dec_i[25] && (~Data_Dec_i[24])) |-> (Data_Bin_o == 5'b00001)
    );

    // If bit 23 is the first low bit, the output maps to 2.
    check_bit23_first_low_maps_to_2: assert property (
        @(posedge clk) ((&Data_Dec_i[25:24]) && (~Data_Dec_i[23])) |-> (Data_Bin_o == 5'b00010)
    );

    // If bit 22 is the first low bit, the output maps to 3.
    check_bit22_first_low_maps_to_3: assert property (
        @(posedge clk) ((&Data_Dec_i[25:23]) && (~Data_Dec_i[22])) |-> (Data_Bin_o == 5'b00011)
    );

    // If bit 21 is the first low bit, the output maps to 4.
    check_bit21_first_low_maps_to_4: assert property (
        @(posedge clk) ((&Data_Dec_i[25:22]) && (~Data_Dec_i[21])) |-> (Data_Bin_o == 5'b00100)
    );

    // If bit 20 is the first low bit, the output maps to 5.
    check_bit20_first_low_maps_to_5: assert property (
        @(posedge clk) ((&Data_Dec_i[25:21]) && (~Data_Dec_i[20])) |-> (Data_Bin_o == 5'b00101)
    );

    // If bit 19 is the first low bit, the output maps to 6.
    check_bit19_first_low_maps_to_6: assert property (
        @(posedge clk) ((&Data_Dec_i[25:20]) && (~Data_Dec_i[19])) |-> (Data_Bin_o == 5'b00110)
    );

    // If bit 18 is the first low bit, the output maps to 7.
    check_bit18_first_low_maps_to_7: assert property (
        @(posedge clk) ((&Data_Dec_i[25:19]) && (~Data_Dec_i[18])) |-> (Data_Bin_o == 5'b00111)
    );

    // If bit 17 is the first low bit, the output maps to 8.
    check_bit17_first_low_maps_to_8: assert property (
        @(posedge clk) ((&Data_Dec_i[25:18]) && (~Data_Dec_i[17])) |-> (Data_Bin_o == 5'b01000)
    );

    // If bit 16 is the first low bit, the output maps to 9.
    check_bit16_first_low_maps_to_9: assert property (
        @(posedge clk) ((&Data_Dec_i[25:17]) && (~Data_Dec_i[16])) |-> (Data_Bin_o == 5'b01001)
    );

    // If bit 15 is the first low bit, the output maps to 10.
    check_bit15_first_low_maps_to_10: assert property (
        @(posedge clk) ((&Data_Dec_i[25:16]) && (~Data_Dec_i[15])) |-> (Data_Bin_o == 5'b01010)
    );

    // If bit 14 is the first low bit, the output maps to 11.
    check_bit14_first_low_maps_to_11: assert property (
        @(posedge clk) ((&Data_Dec_i[25:15]) && (~Data_Dec_i[14])) |-> (Data_Bin_o == 5'b01011)
    );

    // If bit 13 is the first low bit, the output maps to 12.
    check_bit13_first_low_maps_to_12: assert property (
        @(posedge clk) ((&Data_Dec_i[25:14]) && (~Data_Dec_i[13])) |-> (Data_Bin_o == 5'b01100)
    );

    // If bit 12 is the first low bit, the output maps to 13.
    check_bit12_first_low_maps_to_13: assert property (
        @(posedge clk) ((&Data_Dec_i[25:13]) && (~Data_Dec_i[12])) |-> (Data_Bin_o == 5'b01101)
    );

    // If bit 11 is the first low bit, the output maps to 14.
    check_bit11_first_low_maps_to_14: assert property (
        @(posedge clk) ((&Data_Dec_i[25:12]) && (~Data_Dec_i[11])) |-> (Data_Bin_o == 5'b01110)
    );

    // If bit 10 is the first low bit, the output maps to 15.
    check_bit10_first_low_maps_to_15: assert property (
        @(posedge clk) ((&Data_Dec_i[25:11]) && (~Data_Dec_i[10])) |-> (Data_Bin_o == 5'b01111)
    );

    // If bit 9 is the first low bit, the output maps to 16.
    check_bit9_first_low_maps_to_16: assert property (
        @(posedge clk) ((&Data_Dec_i[25:10]) && (~Data_Dec_i[9])) |-> (Data_Bin_o == 5'b10000)
    );

    // If bit 8 is the first low bit, the output maps to 17.
    check_bit8_first_low_maps_to_17: assert property (
        @(posedge clk) ((&Data_Dec_i[25:9]) && (~Data_Dec_i[8])) |-> (Data_Bin_o == 5'b10001)
    );

    // If bit 7 is the first low bit, the output maps to 18.
    check_bit7_first_low_maps_to_18: assert property (
        @(posedge clk) ((&Data_Dec_i[25:8]) && (~Data_Dec_i[7])) |-> (Data_Bin_o == 5'b10010)
    );

    // If bit 6 is the first low bit, the output maps to 19.
    check_bit6_first_low_maps_to_19: assert property (
        @(posedge clk) ((&Data_Dec_i[25:7]) && (~Data_Dec_i[6])) |-> (Data_Bin_o == 5'b10011)
    );

    // If bit 5 is the first low bit, the output maps to 20.
    check_bit5_first_low_maps_to_20: assert property (
        @(posedge clk) ((&Data_Dec_i[25:6]) && (~Data_Dec_i[5])) |-> (Data_Bin_o == 5'b10100)
    );

    // If bit 4 is the first low bit, the output maps to 21.
    check_bit4_first_low_maps_to_21: assert property (
        @(posedge clk) ((&Data_Dec_i[25:5]) && (~Data_Dec_i[4])) |-> (Data_Bin_o == 5'b10101)
    );

    // If bit 3 is the first low bit, the output maps to 22.
    check_bit3_first_low_maps_to_22: assert property (
        @(posedge clk) ((&Data_Dec_i[25:4]) && (~Data_Dec_i[3])) |-> (Data_Bin_o == 5'b10110)
    );

    // If bit 2 is the first low bit, the output maps to 23.
    check_bit2_first_low_maps_to_23: assert property (
        @(posedge clk) ((&Data_Dec_i[25:3]) && (~Data_Dec_i[2])) |-> (Data_Bin_o == 5'b10111)
    );

    // If bit 1 is the first low bit, the output maps to 24.
    check_bit1_first_low_maps_to_24: assert property (
        @(posedge clk) ((&Data_Dec_i[25:2]) && (~Data_Dec_i[1])) |-> (Data_Bin_o == 5'b11000)
    );

    // If bit 0 is the first low bit, the output maps to 21 per the RTL.
    check_bit0_first_low_maps_to_21: assert property (
        @(posedge clk) ((&Data_Dec_i[25:1]) && (~Data_Dec_i[0])) |-> (Data_Bin_o == 5'b10101)
    );

    // If all bits are high, the fall-through output is 0.
    check_all_high_maps_to_0: assert property (
        @(posedge clk) (&Data_Dec_i[25:0]) |-> (Data_Bin_o == 5'b00000)
    );

endmodule