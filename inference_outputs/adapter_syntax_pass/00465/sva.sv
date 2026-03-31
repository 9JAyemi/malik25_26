module up_counter_2bit_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [1:0] count
);

    // Reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 2'b00)
    );

    // When enabled, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (count == ($past(count) + 2'b01))
    );

    // When disabled, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (count == $past(count))
    );

    // The counter wraps from 2'b11 back to 2'b00 when enabled.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count == 2'b11) |=> (count == 2'b00)
    );

endmodule