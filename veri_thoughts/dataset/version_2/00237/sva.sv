module power_of_2_detection_sva (
    input logic        clk,
    input logic [15:0] num,
    input logic        is_power_of_2
);

    // Zero must not be flagged as a power of two.
    check_zero_is_not_power_of_two: assert property (
        @(posedge clk) (num == 16'd0) |-> (is_power_of_2 == 1'b0)
    );

    // A one-hot input must be flagged as a power of two.
    check_onehot_input_sets_output: assert property (
        @(posedge clk) $onehot(num) |-> (is_power_of_2 == 1'b1)
    );

    // A nonzero input with multiple bits set must clear the output.
    check_multibit_input_clears_output: assert property (
        @(posedge clk) ((num != 16'd0) && !$onehot(num)) |-> (is_power_of_2 == 1'b0)
    );

    // A high output must only occur for a one-hot input.
    check_high_output_requires_onehot_input: assert property (
        @(posedge clk) (is_power_of_2 == 1'b1) |-> $onehot(num)
    );

    // The output must match the RTL power-of-two detection expression.
    check_output_matches_rtl_expression: assert property (
        @(posedge clk) (is_power_of_2 == (((num != 16'd0) && ((num & (num - 16'd1)) == 16'd0)) ? 1'b1 : 1'b0))
    );

endmodule