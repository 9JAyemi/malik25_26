module accumulator_sva (
    input logic clk,
    input logic reset,          // active-high synchronous reset
    input logic [7:0] in,
    input logic [15:0] out
);
    // On a non-reset cycle, next out equals current out plus in (16-bit wraparound).
    check_add_update: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> out == $past(out) + $past(in)
    );

    // If in is zero and not in reset, out holds its value next cycle.
    check_hold_when_in_zero: assert property (
        @(posedge clk) disable iff (reset) (in == 8'd0) |=> out == $past(out)
    );

    // If in is 1 and not in reset, out increments by 1 next cycle.
    check_increment_by_one: assert property (
        @(posedge clk) disable iff (reset) (in == 8'd1) |=> out == $past(out) + 16'd1
    );

    // If in is 255 and not in reset, out increments by 255 next cycle.
    check_increment_by_255: assert property (
        @(posedge clk) disable iff (reset) (in == 8'hFF) |=> out == $past(out) + 16'd255
    );

    // After a reset cycle, out is zero on the following cycle.
    check_zero_after_reset_cycle: assert property (
        @(posedge clk) disable iff (reset) $past(reset) |-> (out == 16'd0)
    );

    // If two consecutive cycles are not in reset, out equals out from two cycles ago plus the last two inputs.
    check_two_cycle_accumulation: assert property (
        @(posedge clk) disable iff (reset) (!reset && !$past(reset)) |-> (out == $past(out,2) + $past(in,2) + $past(in,1))
    );

    // When not in reset now and previously, the step difference equals previous input.
    check_step_diff_matches_prev_in: assert property (
        @(posedge clk) disable iff (reset) !$past(reset) |-> (out - $past(out)) == $past(in)
    );

    // On reset deassertion (falling edge), out is zero in that cycle.
    check_out_zero_on_reset_fall: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |-> (out == 16'd0)
    );
endmodule