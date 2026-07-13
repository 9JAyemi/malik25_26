module binary_converter_sva (
    input logic        clk,
    input logic [9:0]  input_val,
    input logic [3:0]  binary_val
);

    // Input value 0 maps to output 0.
    check_zero_input_mapping: assert property (
        @(posedge clk) (input_val == 10'd0) |-> (binary_val == 4'd0)
    );

    // Input values 1 through 8 map to their 4-bit value.
    check_midrange_input_mapping: assert property (
        @(posedge clk) ((input_val >= 10'd1) && (input_val <= 10'd8)) |-> (binary_val == input_val[3:0])
    );

    // Input value 9 maps to output 9.
    check_nine_input_mapping: assert property (
        @(posedge clk) (input_val == 10'd9) |-> (binary_val == 4'd9)
    );

    // Unsupported input values drive the default zero output.
    check_default_zero_for_invalid_inputs: assert property (
        @(posedge clk) (input_val > 10'd9) |-> (binary_val == 4'd0)
    );

    // The output never exceeds the highest encoded value.
    check_output_range: assert property (
        @(posedge clk) (binary_val <= 4'd9)
    );

endmodule