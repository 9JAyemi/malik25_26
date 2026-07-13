module binary_counter_sva (
    input logic       clk,
    input logic [3:0] reset,
    input logic [3:0] enable,
    input logic [3:0] count
);

    // Any nonzero reset clears the counter on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk)
        (reset != 4'b0000) |=> (count == 4'b0000)
    );

    // When reset and enable are both nonzero, reset takes priority.
    check_reset_priority_over_enable: assert property (
        @(posedge clk)
        ((reset != 4'b0000) && (enable != 4'b0000)) |=> (count == 4'b0000)
    );

    // With reset low, any nonzero enable increments the counter by one.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff (reset != 4'b0000)
        (enable != 4'b0000) |=> (count == ($past(count) + 4'b0001))
    );

    // With reset low and enable zero, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset != 4'b0000)
        (enable == 4'b0000) |=> (count == $past(count))
    );

    // With reset low, incrementing 4'hF wraps the counter to 4'h0.
    check_wraps_on_overflow: assert property (
        @(posedge clk) disable iff (reset != 4'b0000)
        ((enable != 4'b0000) && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule