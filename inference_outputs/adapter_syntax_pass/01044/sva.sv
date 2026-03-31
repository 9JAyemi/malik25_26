module signal_processor_sva (
    input logic [3:0] in,
    input logic [3:0] out
);

    // Input 0 maps to 0.
    check_in_0_maps_to_0: assert property (
        @($global_clock) (in == 4'd0) |-> (out == 4'd0)
    );

    // Input 1 maps to 2.
    check_in_1_maps_to_2: assert property (
        @($global_clock) (in == 4'd1) |-> (out == 4'd2)
    );

    // Input 2 maps to 4.
    check_in_2_maps_to_4: assert property (
        @($global_clock) (in == 4'd2) |-> (out == 4'd4)
    );

    // Input 3 maps to 6.
    check_in_3_maps_to_6: assert property (
        @($global_clock) (in == 4'd3) |-> (out == 4'd6)
    );

    // Input 4 maps to 16.
    check_in_4_maps_to_16: assert property (
        @($global_clock) (in == 4'd4) |-> (out == 4'd16)
    );

    // Input 5 maps to 25.
    check_in_5_maps_to_25: assert property (
        @($global_clock) (in == 4'd5) |-> (out == 4'd25)
    );

    // Input 6 maps to 36.
    check_in_6_maps_to_36: assert property (
        @($global_clock) (in == 4'd6) |-> (out == 4'd36)
    );

    // Input 7 maps to 49.
    check_in_7_maps_to_49: assert property (
        @($global_clock) (in == 4'd7) |-> (out == 4'd49)
    );

    // Input 8 maps to 4.
    check_in_8_maps_to_4: assert property (
        @($global_clock) (in == 4'd8) |-> (out == 4'd4)
    );

    // Input 9 maps to 2.
    check_in_9_maps_to_2: assert property (
        @($global_clock) (in == 4'd9) |-> (out == 4'd2)
    );

    // Input 10 maps to 1.
    check_in_10_maps_to_1: assert property (
        @($global_clock) (in == 4'd10) |-> (out == 4'd1)
    );

    // Input 11 maps to 1.
    check_in_11_maps_to_1: assert property (
        @($global_clock) (in == 4'd11) |-> (out == 4'd1)
    );

    // Input 12 maps to 1.
    check_in_12_maps_to_1: assert property (
        @($global_clock) (in == 4'd12) |-> (out == 4'd1)
    );

    // Input 13 maps to 1.
    check_in_13_maps_to_1: assert property (
        @($global_clock) (in == 4'd13) |-> (out == 4'd1)
    );

    // Input 14 maps to 1.
    check_in_14_maps_to_1: assert property (
        @($global_clock) (in == 4'd14) |-> (out == 4'd1)
    );

    // Input 15 maps to 0.
    check_in_15_maps_to_0: assert property (
        @($global_clock) (in == 4'd15) |-> (out == 4'd0)
    );

endmodule