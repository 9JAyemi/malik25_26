module top_module_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0] counter_out,
    input logic [15:0] adder_sum,
    input logic overflow,
    input logic [15:0] final_output
);

    // Counter is zero after a reset cycle.
    check_counter_zero_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        $past(reset) |-> (counter_out == 4'b0000)
    );

    // Counter increments by one when enabled.
    check_counter_increments_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset && enable) |-> (counter_out == ($past(counter_out) + 4'd1))
    );

    // Counter holds its value when not enabled.
    check_counter_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset && !enable) |-> (counter_out == $past(counter_out))
    );

    // Adder sum matches the 16-bit addition of A and B.
    check_adder_sum_matches_addition: assert property (
        @(posedge clk) disable iff (reset)
        adder_sum == (A + B)
    );

    // Overflow follows the implemented signed overflow equation.
    check_overflow_matches_signed_equation: assert property (
        @(posedge clk) disable iff (reset)
        overflow == ((A[15] & B[15] & ~adder_sum[15]) | (~A[15] & ~B[15] & adder_sum[15]))
    );

    // final_output selects the larger of counter_out and adder_sum.
    check_final_output_selects_larger_value: assert property (
        @(posedge clk) disable iff (reset)
        final_output == ((counter_out > adder_sum) ? counter_out : adder_sum)
    );

    // final_output matches the implemented conditional expression.
    check_final_output_matches_conditional_expression: assert property (
        @(posedge clk) disable iff (reset)
        final_output == (counter_out > adder_sum ? counter_out : adder_sum)
    );

endmodule