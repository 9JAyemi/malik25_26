module counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);

    // Low reset clears the counter on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk)
        (reset == 1'b0) |=> (count == 4'd0)
    );

    // When enabled below 15, the counter increments by one.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
        (enable == 1'b1 && count != 4'd15) |=> (count == ($past(count) + 4'd1))
    );

    // When enabled at 15, the counter wraps to zero.
    check_count_wraps_to_zero: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
        (enable == 1'b1 && count == 4'd15) |=> (count == 4'd0)
    );

    // When disabled, the counter holds its value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
        (enable == 1'b0) |=> $stable(count)
    );

endmodule