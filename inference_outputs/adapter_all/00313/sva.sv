module threshold_module_sva #(
    parameter int THRESHOLD = 10
) (
    input logic [3:0] input_value,
    input logic [1:0] output_value
);

    // Output must be one of the three encodings.
    check_output_encoding: assert property (
        @($global_clock) output_value inside {2'b00, 2'b01, 2'b10}
    );

    // Input 0 maps to 2'b00.
    check_map_input_0: assert property (
        @($global_clock) (input_value == 4'd0) |-> (output_value == 2'b00)
    );

    // Input 1 maps to 2'b00.
    check_map_input_1: assert property (
        @($global_clock) (input_value == 4'd1) |-> (output_value == 2'b00)
    );

    // Input 2 maps to 2'b00.
    check_map_input_2: assert property (
        @($global_clock) (input_value == 4'd2) |-> (output_value == 2'b00)
    );

    // Input 3 maps to 2'b00.
    check_map_input_3: assert property (
        @($global_clock) (input_value == 4'd3) |-> (output_value == 2'b00)
    );

    // Input 4 maps to 2'b00.
    check_map_input_4: assert property (
        @($global_clock) (input_value == 4'd4) |-> (output_value == 2'b00)
    );

    // Input 5 maps to 2'b00.
    check_map_input_5: assert property (
        @($global_clock) (input_value == 4'd5) |-> (output_value == 2'b00)
    );

    // Input 6 maps to 2'b01.
    check_map_input_6: assert property (
        @($global_clock) (input_value == 4'd6) |-> (output_value == 2'b01)
    );

    // Input 7 maps to 2'b01.
    check_map_input_7: assert property (
        @($global_clock) (input_value == 4'd7) |-> (output_value == 2'b01)
    );

    // Input 8 maps to 2'b01.
    check_map_input_8: assert property (
        @($global_clock) (input_value == 4'd8) |-> (output_value == 2'b01)
    );

    // Input 9 maps to 2'b01.
    check_map_input_9: assert property (
        @($global_clock) (input_value == 4'd9) |-> (output_value == 2'b01)
    );

    // Input 10 maps to 2'b10.
    check_map_input_10: assert property (
        @($global_clock) (input_value == 4'd10) |-> (output_value == 2'b10)
    );

    // Input 11 maps to 2'b10.
    check_map_input_11: assert property (
        @($global_clock) (input_value == 4'd11) |-> (output_value == 2'b10)
    );

    // Input 12 maps to 2'b10.
    check_map_input_12: assert property (
        @($global_clock) (input_value == 4'd12) |-> (output_value == 2'b10)
    );

    // Input 13 maps to 2'b10.
    check_map_input_13: assert property (
        @($global_clock) (input_value == 4'd13) |-> (output_value == 2'b10)
    );

    // Input 14 maps to 2'b10.
    check_map_input_14: assert property (
        @($global_clock) (input_value == 4'd14) |-> (output_value == 2'b10)
    );

    // Input 15 maps to 2'b10.
    check_map_input_15: assert property (
        @($global_clock) (input_value == 4'd15) |-> (output_value == 2'b10)
    );

endmodule