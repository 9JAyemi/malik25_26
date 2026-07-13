module top_module_sva (
    input logic        clk,
    input logic        reset,
    input logic        enable,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0]  counter_out,
    input logic [15:0] adder_sum,
    input logic        overflow,
    input logic [15:0] final_output
);

    // Counter increments by one when enabled.
    check_counter_increment: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> counter_out == ($past(counter_out) + 4'd1)
    );

    // Counter holds its value when disabled.
    check_counter_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> counter_out == $past(counter_out)
    );

    // Counter is zero on the first cycle after reset.
    check_counter_zero_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        $past(reset) |-> counter_out == 4'b0000
    );

    // Adder sum matches A + B.
    check_adder_sum_matches_inputs: assert property (
        @(posedge clk) disable iff (reset)
        adder_sum == (A + B)
    );

    // Overflow matches the implemented overflow equation.
    check_overflow_matches_equation: assert property (
        @(posedge clk) disable iff (reset)
        overflow == ((A[15] & B[15] & ~adder_sum[15]) | (~A[15] & ~B[15] & adder_sum[15]))
    );

    // Overflow requires same-sign operands and a flipped result sign.
    check_overflow_requires_signed_wrap: assert property (
        @(posedge clk) disable iff (reset)
        overflow |-> ((A[15] == B[15]) && (adder_sum[15] != A[15]))
    );

    // Opposite-sign operands cannot assert overflow.
    check_no_overflow_for_opposite_signs: assert property (
        @(posedge clk) disable iff (reset)
        (A[15] != B[15]) |-> !overflow
    );

    // Final output matches the implemented comparison and selection.
    check_final_output_matches_selection: assert property (
        @(posedge clk) disable iff (reset)
        final_output == (({12'b0, counter_out} > adder_sum) ? {12'b0, counter_out} : adder_sum)
    );

endmodule