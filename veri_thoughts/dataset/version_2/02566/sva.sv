module counter_sva (
    input logic clk,
    input logic rst,          // active-high synchronous reset
    input logic [7:0] count
);
    parameter int unsigned MAX_COUNT = 255;

    ///// Reset behavior /////
    // After reset deassertion, count is 0 on that cycle.
    reset_deassert_zero: assert property (
        @(posedge clk) disable iff (rst) ($past(rst,1) == 1'b1) |-> (count == 8'd0)
    );

    ///// Next-state function /////
    // When not at MAX_COUNT, count increments by 1 next cycle.
    increment_when_below_max: assert property (
        @(posedge clk) disable iff (rst) (count != MAX_COUNT) |=> (count == $past(count) + 8'd1)
    );
    // When at MAX_COUNT, count wraps to 0 next cycle.
    wrap_on_max: assert property (
        @(posedge clk) disable iff (rst) (count == MAX_COUNT) |=> (count == 8'd0)
    );

    ///// Invariants /////
    // While not in reset, count never exceeds MAX_COUNT.
    count_bounded_by_max: assert property (
        @(posedge clk) disable iff (rst) (count <= MAX_COUNT)
    );

    ///// Transition consistency /////
    // If current count != 0 and previous cycle wasn't in reset, previous count was current-1.
    prev_is_one_less_when_curr_nonzero: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && (count != 8'd0)) |-> ($past(count) == (count - 8'd1))
    );
    // If current count is 0 and previous cycle wasn't in reset, previous count was MAX_COUNT.
    zero_only_from_wrap: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && (count == 8'd0)) |-> ($past(count) == MAX_COUNT)
    );
    // MAX_COUNT cannot persist for two consecutive cycles when not in reset.
    no_two_cycles_at_max: assert property (
        @(posedge clk) disable iff (rst) (count == MAX_COUNT) |=> (count != MAX_COUNT)
    );
    // If previous cycle wasn't reset and wasn't MAX_COUNT, current count cannot be 0.
    no_spurious_zero_without_prev_max: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && ($past(count) != MAX_COUNT)) |-> (count != 8'd0)
    );

    ///// Useful strengthened corner checks (parameter-dependent) /////
    // From MAX_COUNT-1, go to MAX_COUNT next cycle (if MAX_COUNT > 0).
    generate
        if (MAX_COUNT > 0) begin : gen_penultimate_to_max
            penultimate_to_max: assert property (
                @(posedge clk) disable iff (rst) (count == (MAX_COUNT - 1)) |=> (count == MAX_COUNT)
            );
        end
    endgenerate
    // From 0 (not immediately after reset), go to 1 next cycle when running (if MAX_COUNT > 0).
    generate
        if (MAX_COUNT > 0) begin : gen_zero_to_one
            zero_to_one_next: assert property (
                @(posedge clk) disable iff (rst) ((count == 8'd0) && !$past(rst)) |=> (count == 8'd1)
            );
        end
    endgenerate
endmodule