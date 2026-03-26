module binary_up_counter_assertions (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // Clock: clk
    // Reset: reset, active high synchronous
    // Logic: sequential 4-bit binary up counter

    // While reset stays asserted across clocks, the observed count remains zero.
    check_zero_while_reset_held: assert property (
        @(posedge clk) disable iff ($initstate)
        (reset && $past(reset)) |-> (count == 4'd0)
    );

    // On the first cycle after reset was asserted, the observed count is zero.
    check_zero_after_reset_release: assert property (
        @(posedge clk) disable iff ($initstate)
        (!reset && $past(reset)) |-> (count == 4'd0)
    );

    // After any non-reset cycle, the counter increments by one modulo 16.
    check_count_increments_after_non_reset_cycle: assert property (
        @(posedge clk) disable iff ($initstate)
        !$past(reset) |-> (count == ($past(count) + 4'd1))
    );

    // A previous count of 15 wraps to 0 on the next observed cycle.
    check_wraps_from_f_to_0: assert property (
        @(posedge clk) disable iff ($initstate)
        (!$past(reset) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

endmodule