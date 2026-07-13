module BCD_to_Binary_sva (
    input logic [3:0] bcd_in,
    input logic [7:0] bin_out
);

    // 0 maps to 00000000.
    check_bcd_0_maps_to_0: assert property (
        @($global_clock) (bcd_in == 4'd0) |-> (bin_out == 8'b00000000)
    );

    // 1 maps to 00000001.
    check_bcd_1_maps_to_1: assert property (
        @($global_clock) (bcd_in == 4'd1) |-> (bin_out == 8'b00000001)
    );

    // 2 maps to 00000010.
    check_bcd_2_maps_to_2: assert property (
        @($global_clock) (bcd_in == 4'd2) |-> (bin_out == 8'b00000010)
    );

    // 3 maps to 00000011.
    check_bcd_3_maps_to_3: assert property (
        @($global_clock) (bcd_in == 4'd3) |-> (bin_out == 8'b00000011)
    );

    // 4 maps to 00000100.
    check_bcd_4_maps_to_4: assert property (
        @($global_clock) (bcd_in == 4'd4) |-> (bin_out == 8'b00000100)
    );

    // 5 maps to 00000101.
    check_bcd_5_maps_to_5: assert property (
        @($global_clock) (bcd_in == 4'd5) |-> (bin_out == 8'b00000101)
    );

    // 6 maps to 00000110.
    check_bcd_6_maps_to_6: assert property (
        @($global_clock) (bcd_in == 4'd6) |-> (bin_out == 8'b00000110)
    );

    // 7 maps to 00000111.
    check_bcd_7_maps_to_7: assert property (
        @($global_clock) (bcd_in == 4'd7) |-> (bin_out == 8'b00000111)
    );

    // 8 maps to 00001000.
    check_bcd_8_maps_to_8: assert property (
        @($global_clock) (bcd_in == 4'd8) |-> (bin_out == 8'b00001000)
    );

    // 9 maps to 00001001.
    check_bcd_9_maps_to_9: assert property (
        @($global_clock) (bcd_in == 4'd9) |-> (bin_out == 8'b00001001)
    );

    // Any non-BCD input drives the default zero output.
    check_default_maps_to_0: assert property (
        @($global_clock) (bcd_in > 4'd9) |-> (bin_out == 8'b00000000)
    );

endmodule