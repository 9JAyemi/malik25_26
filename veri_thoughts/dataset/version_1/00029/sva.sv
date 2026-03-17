module binary_counter_assertions(
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] q
);

    // A sampled reset leaves the counter at zero on the next clock.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |=> (q == 4'b0000)
    );

    // An enabled cycle increments the counter by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset) enable |=> (q == ($past(q) + 4'b0001))
    );

    // A disabled cycle holds the counter value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |=> (q == $past(q))
    );

    // The counter wraps from 15 back to 0 when enabled.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset) (enable && (q == 4'b1111)) |=> (q == 4'b0000)
    );

endmodule