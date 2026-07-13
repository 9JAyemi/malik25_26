module absolute_value_calculator_sva (
    input logic clk,
    input logic signed [7:0] input_num,
    input logic [7:0] abs_value
);

    // Output always matches the RTL's conditional function.
    check_absolute_value_function: assert property (
        @(posedge clk)
        abs_value == ((input_num < 0) ? (~input_num + 8'd1) : input_num)
    );

    // Non-negative inputs pass through unchanged.
    check_non_negative_passthrough: assert property (
        @(posedge clk)
        (input_num >= 0) |-> (abs_value == input_num)
    );

    // Negative inputs produce the two's-complement magnitude.
    check_negative_twos_complement: assert property (
        @(posedge clk)
        (input_num < 0) |-> (abs_value == (~input_num + 8'd1))
    );

    // Zero maps to zero.
    check_zero_case: assert property (
        @(posedge clk)
        (input_num == 8'sd0) |-> (abs_value == 8'd0)
    );

    // Negative one maps to one.
    check_negative_one_case: assert property (
        @(posedge clk)
        (input_num == -8'sd1) |-> (abs_value == 8'd1)
    );

    // The most-negative input wraps to 8'h80 in 8-bit two's complement.
    check_min_negative_case: assert property (
        @(posedge clk)
        (input_num == 8'sh80) |-> (abs_value == 8'h80)
    );

    // A stable input must keep the output stable.
    check_stable_input_stable_output: assert property (
        @(posedge clk)
        $stable(input_num) |-> $stable(abs_value)
    );

endmodule