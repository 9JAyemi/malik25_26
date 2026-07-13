module priority_encoder_assertions (
    input logic [7:0] in,
    input logic [2:0] pos
);

    // One-hot bit 0 maps to position 0.
    check_in_0_maps_to_pos_0: assert property (
        @($global_clock) (in == 8'b00000001) |-> (pos == 3'd0)
    );

    // One-hot bit 1 maps to position 1.
    check_in_1_maps_to_pos_1: assert property (
        @($global_clock) (in == 8'b00000010) |-> (pos == 3'd1)
    );

    // One-hot bit 2 maps to position 2.
    check_in_2_maps_to_pos_2: assert property (
        @($global_clock) (in == 8'b00000100) |-> (pos == 3'd2)
    );

    // One-hot bit 3 maps to position 3.
    check_in_3_maps_to_pos_3: assert property (
        @($global_clock) (in == 8'b00001000) |-> (pos == 3'd3)
    );

    // One-hot bit 4 maps to position 4.
    check_in_4_maps_to_pos_4: assert property (
        @($global_clock) (in == 8'b00010000) |-> (pos == 3'd4)
    );

    // One-hot bit 5 maps to position 5.
    check_in_5_maps_to_pos_5: assert property (
        @($global_clock) (in == 8'b00100000) |-> (pos == 3'd5)
    );

    // One-hot bit 6 maps to position 6.
    check_in_6_maps_to_pos_6: assert property (
        @($global_clock) (in == 8'b01000000) |-> (pos == 3'd6)
    );

    // One-hot bit 7 maps to position 7.
    check_in_7_maps_to_pos_7: assert property (
        @($global_clock) (in == 8'b10000000) |-> (pos == 3'd7)
    );

    // Zero input selects the default output of 0.
    check_zero_input_defaults_to_pos_0: assert property (
        @($global_clock) (in == 8'b00000000) |-> (pos == 3'd0)
    );

    // Any non-zero, non-one-hot input selects the default output of 0.
    check_non_onehot_inputs_default_to_pos_0: assert property (
        @($global_clock)
        (
            (in != 8'b00000000) &&
            (in != 8'b00000001) &&
            (in != 8'b00000010) &&
            (in != 8'b00000100) &&
            (in != 8'b00001000) &&
            (in != 8'b00010000) &&
            (in != 8'b00100000) &&
            (in != 8'b01000000) &&
            (in != 8'b10000000)
        ) |-> (pos == 3'd0)
    );

endmodule