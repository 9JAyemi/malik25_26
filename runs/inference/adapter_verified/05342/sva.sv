module top_module_sva (
    input logic clk,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] out,
    input logic [3:0] max_out
);

// out must equal the 4-bit sum of in1 and in2.
    check_out_sum: assert property (
        @(posedge clk) out == (in1 + in2)
    );

// max_out must equal the 4-bit maximum of out and the sum of in1 and in2.
    check_max_out_function: assert property (
        @(posedge clk) max_out == ((out > (in1 + in2)) ? out : (in1 + in2))
    );

// When out is greater than the sum, max_out must equal out.
    check_max_out_selects_out_when_greater: assert property (
        @(posedge clk) (out > (in1 + in2)) |-> (max_out == out)
    );

// When out is less than or equal to the sum, max_out must equal the sum.
    check_max_out_selects_sum_when_not_greater: assert property (
        @(posedge clk) (out <= (in1 + in2)) |-> (max_out == (in1 + in2))
    );

// Equal inputs must drive out and max_out to the same value.
    check_equal_inputs_same_output: assert property (
        @(posedge clk) (in1 == in2) |-> (out == max_out)
    );

// If the sum is zero, max_out must equal out.
    check_zero_sum_out_equals_max_out: assert property (
        @(posedge clk) ((in1 + in2) == 4'h0) |-> (max_out == out)
    );

// If out is zero, max_out must equal the sum.
    check_zero_out_sum_equals_max_out: assert property (
        @(posedge clk) (out == 4'h0) |-> (max_out == (in1 + in2))
    );

// The maximum 4-bit value must drive max_out to itself.
    check_max_value_pass_through: assert property (
        @(posedge clk) (in1 + in2 == 4'hF) |-> (max_out == 4'hF)
    );

endmodule
