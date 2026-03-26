module counter_sva (
    input logic        clk,
    input logic        reset,
    input logic        enable,
    input logic [31:0] max_count,
    input logic [31:0] count
);

    // A reset cycle leaves count at zero on the following cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 32'd0)
    );

    // Count holds when enable is low.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (count == $past(count))
    );

    // Count wraps to zero when enabled at max_count.
    check_wrap_when_at_max: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count == max_count) |=> (count == 32'd0)
    );

    // Count increments by one when enabled away from max_count.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count != max_count) |=> (count == ($past(count) + 32'd1))
    );

endmodule