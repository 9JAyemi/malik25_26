module binary_counter_sva (
    input logic clk,
    input logic rst,      // active-low asynchronous reset
    input logic en,
    input logic [3:0] count
);
    // Reset low forces count to 0 at each clock.
    check_count_reset_value: assert property (
        @(posedge clk) !rst |-> (count == 4'd0)
    );

    // If the previous cycle was in reset, count is 0 now.
    check_count_zero_after_prev_reset: assert property (
        @(posedge clk) $past(!rst, 1, 1'b0) |-> (count == 4'd0)
    );

    // With reset high, current count can only be previous, previous+1, or 0.
    check_allowed_transitions_when_rst_high: assert property (
        @(posedge clk) disable iff (!rst)
            $past(1'b1) |-> ( (count == $past(count)) || (count == ($past(count) + 4'd1)) || (count == 4'd0) )
    );

    // With en=0 and reset high, next count either holds or goes to 0 (if reset asserted between).
    check_next_when_en0_hold_or_reset: assert property (
        @(posedge clk) disable iff (!rst)
            ($past(1'b1) && !en) |=> ( (count == $past(count)) || (count == 4'd0) )
    );

    // With en=1 and reset high, next count is previous+1 or 0 (if reset asserted between).
    check_next_when_en1_inc_or_reset: assert property (
        @(posedge clk) disable iff (!rst)
            ($past(1'b1) && en) |=> ( (count == ($past(count) + 4'd1)) || (count == 4'd0) )
    );

    // With reset high, count never decreases except to 0 (wrap or reset).
    check_no_decrement_except_zero: assert property (
        @(posedge clk) disable iff (!rst)
            ($past(1'b1) && (count < $past(count))) |-> (count == 4'd0)
    );
endmodule