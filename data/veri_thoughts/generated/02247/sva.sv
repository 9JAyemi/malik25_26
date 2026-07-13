module synchronous_counter_sva (
    input logic clk,
    input logic reset,          // active-HIGH asynchronous reset
    input logic [3:0] count
);

    ///// Reset behavior /////
    // While reset is asserted at the clock edge, count must be zero.
    reset_forces_zero: assert property (
        @(posedge clk) reset |-> (count == 4'd0)
    );

    ///// Counting behavior (clocked) /////
    // If previous cycle was not in reset and count was within 0..9, it remains within 0..9.
    range_closed_no_reset: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(count) <= 4'd9)) |-> (count <= 4'd9)
    );

    // No two consecutive 9s when not in reset across the boundary.
    no_back_to_back_nine: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset)) |-> !($past(count) == 4'd9 && count == 4'd9)
    );

    // If count is 0 when not in reset, the previous value must have been 9.
    zero_implies_prev_nine: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && (count == 4'd0)) |-> ($past(count) == 4'd9)
    );

    // From a previous value 0..8 without reset, next is prev+1 or 1 (if async reset occurred mid-cycle).
    prev_lt9_inc_or_one: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(count) <= 4'd8)) |-> ((count == $past(count) + 1) || (count == 4'd1))
    );

    // From a previous value 9 without reset, next is 0 (wrap) or 1 (if async reset occurred mid-cycle).
    prev_nine_zero_or_one: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(count) == 4'd9)) |-> ((count == 4'd0) || (count == 4'd1))
    );

    // On reset deassertion (1->0 at this clock), the counter advances to 1.
    count_one_after_reset_release: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset) && !reset) |-> (count == 4'd1)
    );

    // If the count decreases across cycles without reset, it can only drop to 0 or 1.
    decrease_only_to_zero_or_one: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && (count < $past(count))) |-> ((count == 4'd0) || (count == 4'd1))
    );

    // When count is 9 (not in reset), the next cycle must be 0 or 1.
    next_after_nine_is_zero_or_one: assert property (
        @(posedge clk) disable iff (reset)
            (count == 4'd9) |-> ##1 (count == 4'd0 || count == 4'd1)
    );

    // From previous 0 with no reset, next value is 1.
    prev_zero_advances_to_one: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(count) == 4'd0)) |-> (count == 4'd1)
    );

endmodule