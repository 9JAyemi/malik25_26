module counter_4bit_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    // Synchronous reset clears the counter on the following clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // Reset takes priority over enable when both are asserted.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (reset && enable) |=> (count == 4'b0000)
    );

    // Counter holds its value when enable is low outside reset.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (!enable) |=> (count == $past(count))
    );

    // Counter increments by one when enable is high outside reset.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (count == ($past(count) + 4'b0001))
    );

    // Counter wraps from 15 back to 0 when enabled.
    check_count_rolls_over_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule