module up_counter_4bit_assertions (
    input logic       clk,
    input logic       reset_n,
    input logic       en,
    input logic [3:0] count
);

    // Count is cleared whenever reset is sampled low.
    check_count_cleared_in_reset: assert property (
        @(posedge clk) !reset_n |-> (count == 4'b0000)
    );

    // After a sampled reset cycle, count starts from zero.
    check_zero_after_reset_release: assert property (
        @(posedge clk) disable iff (!reset_n)
        !$initstate && !$past(reset_n) |-> (count == 4'b0000)
    );

    // An enabled cycle increments the counter by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (!reset_n)
        !$initstate && $past(reset_n) && $past(en) |-> (count == ($past(count) + 4'd1))
    );

    // A disabled cycle holds the counter value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!reset_n)
        !$initstate && $past(reset_n) && !$past(en) |-> (count == $past(count))
    );

    // The counter wraps from 15 back to 0 when enabled.
    check_rollover_from_max: assert property (
        @(posedge clk) disable iff (!reset_n)
        !$initstate && $past(reset_n) && $past(en) && ($past(count) == 4'hF) |-> (count == 4'h0)
    );

    // Count changes only after an enabled cycle.
    check_change_requires_enable: assert property (
        @(posedge clk) disable iff (!reset_n)
        !$initstate && $past(reset_n) && (count != $past(count)) |-> $past(en)
    );

endmodule