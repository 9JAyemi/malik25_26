module BCD_to_Binary_sva (
    input logic clk,
    input logic [3:0] bcd,
    input logic [7:0] bin
);

    // BCD 0 maps to binary 0.
    check_bcd_0_maps_to_0: assert property (
        @(posedge clk) (bcd == 4'd0) |-> (bin == 8'd0)
    );

    // BCD 1 maps to binary 1.
    check_bcd_1_maps_to_1: assert property (
        @(posedge clk) (bcd == 4'd1) |-> (bin == 8'd1)
    );

    // BCD 2 maps to binary 2.
    check_bcd_2_maps_to_2: assert property (
        @(posedge clk) (bcd == 4'd2) |-> (bin == 8'd2)
    );

    // BCD 3 maps to binary 3.
    check_bcd_3_maps_to_3: assert property (
        @(posedge clk) (bcd == 4'd3) |-> (bin == 8'd3)
    );

    // BCD 4 maps to binary 4.
    check_bcd_4_maps_to_4: assert property (
        @(posedge clk) (bcd == 4'd4) |-> (bin == 8'd4)
    );

    // BCD 5 maps to binary 5.
    check_bcd_5_maps_to_5: assert property (
        @(posedge clk) (bcd == 4'd5) |-> (bin == 8'd5)
    );

    // BCD 6 maps to binary 6.
    check_bcd_6_maps_to_6: assert property (
        @(posedge clk) (bcd == 4'd6) |-> (bin == 8'd6)
    );

    // BCD 7 maps to binary 7.
    check_bcd_7_maps_to_7: assert property (
        @(posedge clk) (bcd == 4'd7) |-> (bin == 8'd7)
    );

    // BCD 8 maps to binary 8.
    check_bcd_8_maps_to_8: assert property (
        @(posedge clk) (bcd == 4'd8) |-> (bin == 8'd8)
    );

    // BCD 9 maps to binary 9.
    check_bcd_9_maps_to_9: assert property (
        @(posedge clk) (bcd == 4'd9) |-> (bin == 8'd9)
    );

    // Invalid BCD values map to the error code 8'hFF.
    check_invalid_bcd_maps_to_error: assert property (
        @(posedge clk) (bcd >= 4'd10) |-> (bin == 8'hFF)
    );

    // The error code is only produced for invalid BCD values.
    check_error_code_only_for_invalid_bcd: assert property (
        @(posedge clk) (bin == 8'hFF) |-> (bcd >= 4'd10)
    );

endmodule