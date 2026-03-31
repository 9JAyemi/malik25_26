module power_good_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic in5,
    input logic in6,
    input logic in7,
    input logic in8,
    input logic in9,
    input logic out1
);

// out1 equals the 9-input AND of all inputs.
    check_out_matches_and9: assert property (
        @(posedge clk) out1 == (in1 & in2 & in3 & in4 & in5 & in6 & in7 & in8 & in9)
    );

// If any input is 0, out1 must be 0.
    check_zero_if_any_input_zero: assert property (
        @(posedge clk) ((in1 == 1'b0) || (in2 == 1'b0) || (in3 == 1'b0) || (in4 == 1'b0) || (in5 == 1'b0) || (in6 == 1'b0) || (in7 == 1'b0) || (in8 == 1'b0) || (in9 == 1'b0)) |-> (out1 == 1'b0)
    );

// If all inputs are 1, out1 must be 1.
    check_one_if_all_inputs_one: assert property (
        @(posedge clk) (in1 && in2 && in3 && in4 && in5 && in6 && in7 && in8 && in9) |-> (out1 == 1'b1)
    );

// If out1 is 1, then all inputs must be 1.
    check_all_inputs_one_if_out_one: assert property (
        @(posedge clk) (out1 == 1'b1) |-> (in1 && in2 && in3 && in4 && in5 && in6 && in7 && in8 && in9)
    );

// If out1 is 0, then at least one input must be 0.
    check_any_input_zero_if_out_zero: assert property (
        @(posedge clk) (out1 == 1'b0) |-> ((in1 == 1'b0) || (in2 == 1'b0) || (in3 == 1'b0) || (in4 == 1'b0) || (in5 == 1'b0) || (in6 == 1'b0) || (in7 == 1'b0) || (in8 == 1'b0) || (in9 == 1'b0))
    );

endmodule
