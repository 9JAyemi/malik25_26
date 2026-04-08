module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    // Previous-cycle reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(reset) |-> (count == 4'h0)
    );

    // Reset has priority over enable.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(reset) && $past(enable)) |-> (count == 4'h0)
    );

    // Previous-cycle enable increments the counter by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff ($initstate || (reset && $past(reset)))
        (!$past(reset) && $past(enable)) |-> (count == ($past(count) + 4'h1))
    );

    // With no previous reset or enable, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff ($initstate || (reset && $past(reset)))
        (!$past(reset) && !$past(enable)) |-> (count == $past(count))
    );

    // Any count change must come from a previous reset or enable.
    check_change_has_cause: assert property (
        @(posedge clk) disable iff ($initstate)
        (count != $past(count)) |-> ($past(reset) || $past(enable))
    );

    // Enabling at 4'hF wraps the 4-bit counter to zero.
    check_wraparound_from_max: assert property (
        @(posedge clk) disable iff ($initstate || (reset && $past(reset)))
        (!$past(reset) && $past(enable) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

endmodule