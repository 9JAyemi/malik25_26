module threshold_module_sva #(
    parameter int unsigned THRESHOLD = 10
) (
    input logic clk,
    input logic [3:0] input_value,
    input logic [1:0] output_value
);

    // Inputs at or below 5 drive the low output code.
    check_low_range_output: assert property (
        @(posedge clk) (input_value <= 4'd5) |-> (output_value == 2'b00)
    );

    // Inputs above 5 and below the threshold drive the middle output code.
    check_mid_range_output: assert property (
        @(posedge clk) ((input_value > 4'd5) && (input_value < THRESHOLD)) |-> (output_value == 2'b01)
    );

    // Inputs above 5 and at or above the threshold drive the high output code.
    check_high_range_output: assert property (
        @(posedge clk) ((input_value > 4'd5) && (input_value >= THRESHOLD)) |-> (output_value == 2'b10)
    );

    // The low output code only occurs when the input is at or below 5.
    check_low_code_condition: assert property (
        @(posedge clk) (output_value == 2'b00) |-> (input_value <= 4'd5)
    );

    // The middle output code only occurs for inputs between 5 and the threshold.
    check_mid_code_condition: assert property (
        @(posedge clk) (output_value == 2'b01) |-> ((input_value > 4'd5) && (input_value < THRESHOLD))
    );

    // The high output code only occurs for inputs above 5 and at or above the threshold.
    check_high_code_condition: assert property (
        @(posedge clk) (output_value == 2'b10) |-> ((input_value > 4'd5) && (input_value >= THRESHOLD))
    );

    // The output never uses the unused 2'b11 encoding.
    check_output_encoding: assert property (
        @(posedge clk) (output_value != 2'b11)
    );

endmodule