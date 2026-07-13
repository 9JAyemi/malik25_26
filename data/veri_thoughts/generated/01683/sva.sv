module binary_counter_sva #(
    parameter int n = 4
)(
    input logic clk,
    input logic rst,             // active-high synchronous reset
    input logic [n-1:0] count    // n-bit up-counter
);

    // On a cycle with rst HIGH, next cycle count must be 0.
    reset_clears_next: assert property (
        @(posedge clk) rst |=> (count == '0)
    );

    // While rst is held HIGH across consecutive cycles, count stays 0.
    reset_holds_zero: assert property (
        @(posedge clk) rst && $past(rst) |-> (count == '0)
    );

    // When two consecutive cycles are out of reset, count increments by 1.
    count_increments_when_free: assert property (
        @(posedge clk) disable iff (rst) (!rst && !$past(rst)) |-> (count == $past(count) + 1)
    );

    // Immediately after reset deasserts, count increments from the prior value (which was 0).
    increment_after_reset_deassert: assert property (
        @(posedge clk) $fell(rst) |-> (count == $past(count) + 1)
    );

    // When previous value was all 1s and not in reset, wrap to 0 on increment.
    wrap_on_max: assert property (
        @(posedge clk) disable iff (rst) (!rst && !$past(rst) && ($past(count) == '1)) |-> (count == '0)
    );

    // LSB toggles each cycle when out of reset for consecutive cycles.
    lsb_toggles_no_reset: assert property (
        @(posedge clk) disable iff (rst) (!rst && !$past(rst)) |-> (count[0] == ~$past(count[0]))
    );

    // If previous value was not max and no reset, the result cannot be 0.
    no_spurious_zero_without_wrap: assert property (
        @(posedge clk) disable iff (rst) (!rst && !$past(rst) && ($past(count) != '1)) |-> (count != '0)
    );

    // Across two consecutive out-of-reset cycles, count increases by 2 (mod 2^n).
    two_cycle_increment: assert property (
        @(posedge clk) disable iff (rst) (!rst && !$past(rst) && !$past(rst,2)) |-> (count == $past(count,2) + 2)
    );

endmodule