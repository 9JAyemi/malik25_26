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

    // When enabled outside reset, the counter increments by one.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (reset) enable |-> (count == ($past(count) + 2'b01))
    );

    // When not enabled outside reset, the counter holds its value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |-> (count == $past(count))
    );

    // The 2-bit counter wraps from 3 to 0 when enabled.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset) (enable && (count == 2'b11)) |-> (count == 2'b00)
    );

endmodule