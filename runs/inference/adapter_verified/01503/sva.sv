module fsm_rising_edge_counter_sva (
    input logic clk,
    input logic in,
    input logic [2:0] count
);

// Clock: clk (posedge). No reset in RTL. Sequential counter with IDLE and COUNT states.

    // In IDLE, a rising edge increments count to 0 and enters COUNT.
    check_idle_to_count_on_rise: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == IDLE) && in && !d_last |=> (state == COUNT) && (count == 3'd0)
    );

// In COUNT, a rising edge increments count by 1 (up to 4) and stays in COUNT.
    check_count_increments_on_rise: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == COUNT) && in && !d_last |=> (state == COUNT) && (count inside {3'd0,3'd1,3'd2,3'd3,3'd4})
    );

// In COUNT, a non-rising edge returns to IDLE.
    check_count_to_idle_on_no_rise: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == COUNT) && !in |=> (state == IDLE)
    );

// In COUNT, count 4 wraps to 0 and stays in COUNT.
    check_count_wraps_to_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == COUNT) && in && !d_last && (count == 3'd4) |=> (state == COUNT) && (count == 3'd0)
    );

// In COUNT, count 4 with a non-rising edge returns to IDLE.
    check_count_to_idle_on_no_rise_after_max: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == COUNT) && (count == 3'd4) && !in |=> (state == IDLE)
    );

// In IDLE, a non-rising edge stays in IDLE.
    check_idle_stays_idle_on_no_rise: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == IDLE) && !in |=> (state == IDLE)
    );

// In IDLE, a non-rising edge leaves count unchanged.
    check_idle_count_holds_on_no_rise: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == IDLE) && !in |=> (count == $past(count))
    );

// In COUNT, a non-rising edge leaves count unchanged.
    check_count_holds_on_no_rise: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == COUNT) && !in |=> (count == $past(count))
    );

endmodule
