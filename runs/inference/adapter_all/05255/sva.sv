module binary_multiplier_sva (
    input logic clk,
    input logic reset,
    input logic [15:0] a,
    input logic [15:0] b,
    input logic [31:0] result
);
    // On reset, result is cleared to zero on the next cycle.
    reset_clears_result_next: assert property (
        @(posedge clk) reset |=> (result == 32'd0)
    );

    // When not in reset, result equals the product of a and b from the previous cycle.
    result_matches_prev_product: assert property (
        @(posedge clk) disable iff (reset) result == $past(a * b)
    );

    // If a is zero in the previous cycle and not in reset now, result is zero now.
    zero_a_prev_implies_zero_result_now: assert property (
        @(posedge clk) disable iff (reset) ($past(a) == 16'd0) |-> (result == 32'd0)
    );

    // If b is zero in the previous cycle and not in reset now, result is zero now.
    zero_b_prev_implies_zero_result_now: assert property (
        @(posedge clk) disable iff (reset) ($past(b) == 16'd0) |-> (result == 32'd0)
    );

    // If a is one in the previous cycle and not in reset now, result equals previous b.
    one_a_prev_implies_result_eq_prev_b: assert property (
        @(posedge clk) disable iff (reset) ($past(a) == 16'd1) |-> (result == $past(b))
    );

    // If b is one in the previous cycle and not in reset now, result equals previous a.
    one_b_prev_implies_result_eq_prev_a: assert property (
        @(posedge clk) disable iff (reset) ($past(b) == 16'd1) |-> (result == $past(a))
    );

    // If a and b are stable over the last two cycles and not in reset now, result is stable now.
    stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (reset) ($stable(a) && $stable(b) && !$past(reset)) |-> $stable(result)
    );

    // If a is zero now and not in reset now, result is zero now (previous a was zero).
    zero_a_now_implies_zero_result_now: assert property (
        @(posedge clk) disable iff (reset) (a == 16'd0) |-> (result == 32'd0)
    );

    // If b is zero now and not in reset now, result is zero now (previous b was zero).
    zero_b_now_implies_zero_result_now: assert property (
        @(posedge clk) disable iff (reset) (b == 16'd0) |-> (result == 32'd0)
    );

    // If a is one now and not in reset now, result equals previous b.
    one_a_now_implies_result_eq_prev_b: assert property (
        @(posedge clk) disable iff (reset) (a == 16'd1) |-> (result == $past(b))
    );

    // If b is one now and not in reset now, result equals previous a.
    one_b_now_implies_result_eq_prev_a: assert property (
        @(posedge clk) disable iff (reset) (b == 16'd1) |-> (result == $past(a))
    );
endmodule