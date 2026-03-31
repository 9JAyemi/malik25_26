module threshold_module_sva #(
    parameter int THRESHOLD = 10
) (
    input logic [3:0] input_value,
    input logic [1:0] output_value
);

    // Output is always one of the three encodings.
    check_output_encoding: assert property (
        @($global_clock) output_value inside {2'b00, 2'b01, 2'b10}
    );

    // Input values 0 through 5 map to 00.
    check_low_range_encoding: assert property (
        @($global_clock) (input_value <= 4'd5) |-> (output_value == 2'b00)
    );

    // Input values above the threshold map to 10.
    check_high_range_encoding: assert property (
        @($global_clock) (input_value >= THRESHOLD) |-> (output_value == 2'b10)
    );

    // Input values in the 6 to 9 range map to 01.
    check_mid_range_encoding: assert property (
        @($global_clock) ((input_value >= 4'd6) && (input_value <= 4'd9)) |-> (output_value == 2'b01)
    );

    // 00 can only come from input values 0 through 5.
    check_low_range_decode: assert property (
        @($global_clock) (output_value == 2'b00) |-> (input_value <= 4'd5)
    );

    // 10 can only come from input values above the threshold.
    check_high_range_decode: assert property (
        @($global_clock) (output_value == 2'b10) |-> (input_value >= THRESHOLD)
    );

    // 01 can only come from input values in the 6 to 9 range.
    check_mid_range_decode: assert property (
        @($global_clock) (output_value == 2'b01) |-> ((input_value >= 4'd6) && (input_value <= 4'd9))
    );

endmodule