module counter_4bit_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);

    // Active-low reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !reset |-> (count == 4'h0)
    );

    // When enabled, the counter increments by one on the next clock.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (!reset)
        enable |=> (count == ($past(count) + 4'd1))
    );

    // When disabled, the counter holds its value on the next clock.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!reset)
        !enable |=> (count == $past(count))
    );

    // The counter wraps from 15 back to 0 when enabled.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (!reset)
        (enable && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule