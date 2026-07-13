module decimal_to_binary_sva (
    input logic        clk,
    input logic [3:0]  in_value,
    input logic [3:0]  out_value
);

    // Valid decimal inputs pass through unchanged.
    check_valid_decimal_passthrough: assert property (
        @(posedge clk)
        ((in_value == 4'd0) || (in_value == 4'd1) || (in_value == 4'd2) || (in_value == 4'd3) ||
         (in_value == 4'd4) || (in_value == 4'd5) || (in_value == 4'd6) || (in_value == 4'd7) ||
         (in_value == 4'd8) || (in_value == 4'd9))
        |-> (out_value == in_value)
    );

    // Input 0 maps to output 0.
    check_digit_0_identity: assert property (
        @(posedge clk)
        (in_value == 4'd0) |-> (out_value == 4'd0)
    );

    // Input 1 maps to output 1.
    check_digit_1_identity: assert property (
        @(posedge clk)
        (in_value == 4'd1) |-> (out_value == 4'd1)
    );

    // Input 2 maps to output 2.
    check_digit_2_identity: assert property (
        @(posedge clk)
        (in_value == 4'd2) |-> (out_value == 4'd2)
    );

    // Input 3 maps to output 3.
    check_digit_3_identity: assert property (
        @(posedge clk)
        (in_value == 4'd3) |-> (out_value == 4'd3)
    );

    // Input 4 maps to output 4.
    check_digit_4_identity: assert property (
        @(posedge clk)
        (in_value == 4'd4) |-> (out_value == 4'd4)
    );

    // Input 5 maps to output 5.
    check_digit_5_identity: assert property (
        @(posedge clk)
        (in_value == 4'd5) |-> (out_value == 4'd5)
    );

    // Input 6 maps to output 6.
    check_digit_6_identity: assert property (
        @(posedge clk)
        (in_value == 4'd6) |-> (out_value == 4'd6)
    );

    // Input 7 maps to output 7.
    check_digit_7_identity: assert property (
        @(posedge clk)
        (in_value == 4'd7) |-> (out_value == 4'd7)
    );

    // Input 8 maps to output 8.
    check_digit_8_identity: assert property (
        @(posedge clk)
        (in_value == 4'd8) |-> (out_value == 4'd8)
    );

    // Input 9 maps to output 9.
    check_digit_9_identity: assert property (
        @(posedge clk)
        (in_value == 4'd9) |-> (out_value == 4'd9)
    );

endmodule