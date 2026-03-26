module top_module_assertions (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic [15:0] data,
    input logic [3:0]  shift_amount,
    input logic        direction,
    input logic [15:0] q
);

    // No DUT clock or reset; clk is an external sampling clock for this combinational RTL.
    // A and B form a 4-bit sum, data is shifted by shift_amount based on direction, and q adds both results.

    // In left mode, q is the left-shifted data plus the 4-bit sum of A and B.
    check_left_mode_result: assert property (
        @(posedge clk) (direction == 1'b0) |-> (q == ((data << shift_amount) + (A + B)))
    );

    // In right mode, q is the right-shifted data plus the 4-bit sum of A and B.
    check_right_mode_result: assert property (
        @(posedge clk) (direction == 1'b1) |-> (q == ((data >> shift_amount) + (A + B)))
    );

    // A zero shift amount passes data unchanged into the final addition.
    check_zero_shift_result: assert property (
        @(posedge clk) (shift_amount == 4'd0) |-> (q == (data + (A + B)))
    );

    // When the 4-bit sum is zero, left mode depends only on the shifter result.
    check_zero_sum_left_result: assert property (
        @(posedge clk) ((direction == 1'b0) && ((A + B) == 4'd0)) |-> (q == (data << shift_amount))
    );

    // When the 4-bit sum is zero, right mode depends only on the shifter result.
    check_zero_sum_right_result: assert property (
        @(posedge clk) ((direction == 1'b1) && ((A + B) == 4'd0)) |-> (q == (data >> shift_amount))
    );

    // With zero shift and zero 4-bit sum, q matches data exactly.
    check_zero_shift_zero_sum_passthrough: assert property (
        @(posedge clk) ((shift_amount == 4'd0) && ((A + B) == 4'd0)) |-> (q == data)
    );

    // With zero adder inputs in left mode, q is just the left-shifted data.
    check_zero_operands_left_result: assert property (
        @(posedge clk) ((direction == 1'b0) && (A == 4'd0) && (B == 4'd0)) |-> (q == (data << shift_amount))
    );

    // With zero adder inputs in right mode, q is just the right-shifted data.
    check_zero_operands_right_result: assert property (
        @(posedge clk) ((direction == 1'b1) && (A == 4'd0) && (B == 4'd0)) |-> (q == (data >> shift_amount))
    );

    // Stable inputs keep the combinational output stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) $stable({A, B, data, shift_amount, direction}) |-> $stable(q)
    );

endmodule