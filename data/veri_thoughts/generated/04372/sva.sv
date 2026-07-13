module binary_counter_sva(
    input logic clk,
    input logic [3:0] reset,
    input logic [3:0] enable,
    input logic [3:0] count
);

    // Reset forces count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk)
        (reset == 4'hF) |=> (count == 4'h0)
    );

    // Reset overrides enable when both are asserted.
    check_reset_priority_over_enable: assert property (
        @(posedge clk)
        (reset == 4'hF && enable == 4'hF) |=> (count == 4'h0)
    );

    // Without reset, a non-4'hF enable leaves count unchanged.
    check_hold_when_enable_inactive: assert property (
        @(posedge clk) disable iff (reset == 4'hF)
        (enable != 4'hF) |=> (count == $past(count))
    );

    // With enable active, count increments from non-maximum values.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset == 4'hF)
        (enable == 4'hF && count != 4'hF) |=> (count == ($past(count) + 4'h1))
    );

    // With enable active, count wraps to zero from 4'hF.
    check_wrap_when_enabled_at_max: assert property (
        @(posedge clk) disable iff (reset == 4'hF)
        (enable == 4'hF && count == 4'hF) |=> (count == 4'h0)
    );

endmodule