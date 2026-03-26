module binary_counter_sva (
    input logic reset,
    input logic enable,
    input logic clk,
    input logic [3:0] count
);

    // A sampled reset cycle forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk)
        reset |=> (count == 4'd0)
    );

    // When disabled outside reset, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (count == $past(count))
    );

    // When enabled below 15 outside reset, the counter increments by one.
    check_increment_when_enabled_below_max: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count != 4'd15) |=> (count == ($past(count) + 4'd1))
    );

    // When enabled at 15 outside reset, the counter wraps to zero.
    check_wrap_when_enabled_at_max: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count == 4'd15) |=> (count == 4'd0)
    );

endmodule