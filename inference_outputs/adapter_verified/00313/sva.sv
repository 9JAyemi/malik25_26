module threshold_module_sva (
    input logic clk,
    input logic [3:0] input_value,
    input logic [1:0] output_value
);

// Output is 00 when input is 0 through 5.
    check_low_range_maps_to_zero: assert property (
        @(posedge clk) (input_value <= 4'd5) |-> (output_value == 2'b00)
    );

// Output is 01 when input is 6 through 9.
    check_mid_range_maps_to_one: assert property (
        @(posedge clk) (input_value >= 4'd6 && input_value <= 4'd9) |-> (output_value == 2'b01)
    );

// Output is 10 when input is 10 or higher.
    check_high_range_maps_to_two: assert property (
        @(posedge clk) (input_value >= 4'd10) |-> (output_value == 2'b10)
    );

// Output value is always one of the three implemented encodings.
    check_output_encoding_legal: assert property (
        @(posedge clk) output_value inside {2'b00, 2'b01, 2'b10}
    );

// 00 output implies input is 0 through 5.
    check_zero_output_implies_low_range: assert property (
        @(posedge clk) (output_value == 2'b00) |-> (input_value <= 4'd5)
    );

// 01 output implies input is 6 through 9.
    check_one_output_implies_mid_range: assert property (
        @(posedge clk) (output_value == 2'b01) |-> (input_value >= 4'd6 && input_value <= 4'd9)
    );

// 10 output implies input is 10 or higher.
    check_two_output_implies_high_range: assert property (
        @(posedge clk) (output_value == 2'b10) |-> (input_value >= 4'd10)
    );

endmodule
