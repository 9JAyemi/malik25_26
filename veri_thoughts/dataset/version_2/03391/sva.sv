module counter_assertions (
    input logic       clk,
    input logic       areset,
    input logic       enable,
    input logic [3:0] count
);

    // Counter is zero on the cycle after reset was asserted.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff (areset)
        (!$initstate && $past(areset)) |-> (count == 4'b0000)
    );

    // Reset has priority over enable.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) disable iff (areset)
        (!$initstate && $past(areset && enable)) |-> (count == 4'b0000)
    );

    // Counter increments by one when enabled outside reset.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (areset)
        (!$initstate && !$past(areset) && $past(enable)) |-> (count == ($past(count) + 4'd1))
    );

    // Counter holds its value when not enabled outside reset.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (areset)
        (!$initstate && !$past(areset) && !$past(enable)) |-> (count == $past(count))
    );

    // Any count change outside reset requires enable.
    check_count_changes_require_enable: assert property (
        @(posedge clk) disable iff (areset)
        (!$initstate && !$past(areset) && (count != $past(count))) |-> $past(enable)
    );

    // The 4-bit counter wraps from 15 to 0 when enabled.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (areset)
        (!$initstate && !$past(areset) && $past(enable) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

endmodule