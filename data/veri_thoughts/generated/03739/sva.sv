module BCD_to_Binary_sva (
    input logic clk,
    input logic [3:0] bcd_in,
    input logic [7:0] bin_out
);

    // No clock or reset exists in the RTL; sample this combinational decoder on clk.

    // BCD 0 decodes to binary 0.
    check_bcd_0_maps_to_0: assert property (
        @(posedge clk) (bcd_in == 4'b0000) |-> (bin_out == 8'b00000000)
    );

    // BCD 1 decodes to binary 1.
    check_bcd_1_maps_to_1: assert property (
        @(posedge clk) (bcd_in == 4'b0001) |-> (bin_out == 8'b00000001)
    );

    // BCD 2 decodes to binary 2.
    check_bcd_2_maps_to_2: assert property (
        @(posedge clk) (bcd_in == 4'b0010) |-> (bin_out == 8'b00000010)
    );

    // BCD 3 decodes to binary 3.
    check_bcd_3_maps_to_3: assert property (
        @(posedge clk) (bcd_in == 4'b0011) |-> (bin_out == 8'b00000011)
    );

    // BCD 4 decodes to binary 4.
    check_bcd_4_maps_to_4: assert property (
        @(posedge clk) (bcd_in == 4'b0100) |-> (bin_out == 8'b00000100)
    );

    // BCD 5 decodes to binary 5.
    check_bcd_5_maps_to_5: assert property (
        @(posedge clk) (bcd_in == 4'b0101) |-> (bin_out == 8'b00000101)
    );

    // BCD 6 decodes to binary 6.
    check_bcd_6_maps_to_6: assert property (
        @(posedge clk) (bcd_in == 4'b0110) |-> (bin_out == 8'b00000110)
    );

    // BCD 7 decodes to binary 7.
    check_bcd_7_maps_to_7: assert property (
        @(posedge clk) (bcd_in == 4'b0111) |-> (bin_out == 8'b00000111)
    );

    // BCD 8 decodes to binary 8.
    check_bcd_8_maps_to_8: assert property (
        @(posedge clk) (bcd_in == 4'b1000) |-> (bin_out == 8'b00001000)
    );

    // BCD 9 decodes to binary 9.
    check_bcd_9_maps_to_9: assert property (
        @(posedge clk) (bcd_in == 4'b1001) |-> (bin_out == 8'b00001001)
    );

    // Inputs outside valid BCD range use the default zero output.
    check_invalid_bcd_maps_to_zero: assert property (
        @(posedge clk) (bcd_in > 4'd9) |-> (bin_out == 8'b00000000)
    );

    // The output never exceeds the implemented 0-to-9 range.
    check_bin_out_range: assert property (
        @(posedge clk) (bin_out <= 8'd9)
    );

endmodule