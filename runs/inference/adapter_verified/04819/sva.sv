module multiplier_sva (
    input logic signed [7:0] a,
    input logic signed [7:0] b,
    input logic sel,
    input logic reset,
    input logic clk,
    input logic signed [15:0] out
);

// Reset clears the registered outputs on the next clock.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |=> (out == 16'sd0)
    );

// In add mode, out captures a + b on the next clock.
    check_add_mode_result: assert property (
        @(posedge clk) disable iff (reset)
        (!sel) |=> (out == ($past(a) + $past(b)))
    );

// In multiply mode, out captures a * b on the next clock.
    check_multiply_mode_result: assert property (
        @(posedge clk) disable iff (reset)
        sel |=> (out == ($past(a) * $past(b)))
    );

// With sel high and equal operands, out is twice the operand value.
    check_add_equal_operands: assert property (
        @(posedge clk) disable iff (reset)
        (sel && (a == b)) |=> (out == ($past(a) << 1))
    );

// With sel high and zero on b, out is zero.
    check_add_zero_b: assert property (
        @(posedge clk) disable iff (reset)
        (sel && (b == 8'sd0)) |=> (out == 16'sd0)
    );

// With sel high and zero on a, out is zero.
    check_add_zero_a: assert property (
        @(posedge clk) disable iff (reset)
        (sel && (a == 8'sd0)) |=> (out == 16'sd0)
    );

// With sel low and equal operands, out is the square of the operand.
    check_multiply_equal_operands: assert property (
        @(posedge clk) disable iff (reset)
        (!sel && (a == b)) |=> (out == ($past(a) * $past(a)))
    );

// With sel low and zero on b, out is zero.
    check_multiply_zero_b: assert property (
        @(posedge clk) disable iff (reset)
        (!sel && (b == 8'sd0)) |=> (out == 16'sd0)
    );

// With sel low and zero on a, out is zero.
    check_multiply_zero_a: assert property (
        @(posedge clk) disable iff (reset)
        (!sel && (a == 8'sd0)) |=> (out == 16'sd0)
    );

endmodule
