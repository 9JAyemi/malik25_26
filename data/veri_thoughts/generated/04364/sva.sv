module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);

    // Reset clears the counter to zero by the next sampled clock.
    check_reset_clears_count: assert property (
        @(posedge clk)
        reset |=> (count == 4'b0000)
    );

    // When enabled, the counter increments by one.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (count == ($past(count) + 4'b0001))
    );

    // When disabled, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (count == $past(count))
    );

    // The 4-bit counter wraps from 15 back to 0 when enabled.
    check_wrap_from_f_to_0: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count == 4'hF) |=> (count == 4'h0)
    );

endmodule