module BCD_to_Binary_sva (
    input logic clk,
    input logic [3:0] bcd,
    input logic [3:0] bin
);

    // BCD 0 maps to binary 0.
    check_bcd_0_maps_to_bin_0: assert property (
        @(posedge clk) (bcd == 4'b0000) |-> (bin == 4'b0000)
    );

    // BCD 1 maps to binary 1.
    check_bcd_1_maps_to_bin_1: assert property (
        @(posedge clk) (bcd == 4'b0001) |-> (bin == 4'b0001)
    );

    // BCD 2 maps to binary 2.
    check_bcd_2_maps_to_bin_2: assert property (
        @(posedge clk) (bcd == 4'b0010) |-> (bin == 4'b0010)
    );

    // BCD 3 maps to binary 3.
    check_bcd_3_maps_to_bin_3: assert property (
        @(posedge clk) (bcd == 4'b0011) |-> (bin == 4'b0011)
    );

    // BCD 4 maps to binary 4.
    check_bcd_4_maps_to_bin_4: assert property (
        @(posedge clk) (bcd == 4'b0100) |-> (bin == 4'b0100)
    );

    // BCD 5 maps to binary 5.
    check_bcd_5_maps_to_bin_5: assert property (
        @(posedge clk) (bcd == 4'b0101) |-> (bin == 4'b0101)
    );

    // BCD 6 maps to binary 6.
    check_bcd_6_maps_to_bin_6: assert property (
        @(posedge clk) (bcd == 4'b0110) |-> (bin == 4'b0110)
    );

    // BCD 7 maps to binary 7.
    check_bcd_7_maps_to_bin_7: assert property (
        @(posedge clk) (bcd == 4'b0111) |-> (bin == 4'b0111)
    );

    // BCD 8 maps to binary 8.
    check_bcd_8_maps_to_bin_8: assert property (
        @(posedge clk) (bcd == 4'b1000) |-> (bin == 4'b1000)
    );

    // BCD 9 maps to binary 9.
    check_bcd_9_maps_to_bin_9: assert property (
        @(posedge clk) (bcd == 4'b1001) |-> (bin == 4'b1001)
    );

endmodule