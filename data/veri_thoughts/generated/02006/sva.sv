module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // When reset is high, count must be 0.
    reset_clears_count: assert property (
        @(posedge clk) rst |-> (count == 4'd0)
    );

    // From any non-15 value, next count increments by 1.
    increment_nonmax: assert property (
        @(posedge clk) disable iff (rst) (count != 4'd15) |-> ##1 (count == $past(count) + 4'd1)
    );

    // From 15, next count wraps to 0.
    wrap_on_max: assert property (
        @(posedge clk) disable iff (rst) (count == 4'd15) |-> ##1 (count == 4'd0)
    );

    // LSB toggles every active cycle.
    lsb_toggles: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> ##1 (count[0] == ~$past(count[0]))
    );

    // Count changes every active cycle (no stutter).
    progress_no_stall: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> ##1 (count != $past(count))
    );

    // A zero value without reset implies previous was 15.
    zero_implies_prev_15: assert property (
        @(posedge clk) disable iff (rst) (count == 4'd0 && !$past(rst)) |-> ($past(count) == 4'd15)
    );

    // Counter is 16-cycle periodic when no reset intervenes.
    period_16: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> ##16 (count == $past(count,16))
    );

    // When lower 3 bits roll over, MSB toggles and lower bits clear.
    msb_toggle_on_lower_roll: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && ($past(count[2:0]) == 3'b111)) |-> (count[3] == ~$past(count[3]) && count[2:0] == 3'b000)
    );

endmodule