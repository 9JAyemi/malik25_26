module counter_4bit_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);
    // While reset is asserted low, count must be 0.
    reset_forces_zero: assert property (
        @(posedge clk) !reset |-> (count == 4'd0)
    );

    // When enable is HIGH, count increments by 1 on the next cycle.
    increment_on_enable: assert property (
        @(posedge clk) disable iff (!reset) enable |=> (count == $past(count) + 4'd1)
    );

    // When enable is LOW, count holds its value on the next cycle.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (!reset) !enable |=> (count == $past(count))
    );

    // Any change in count (excluding reset) requires enable to be HIGH.
    change_requires_enable: assert property (
        @(posedge clk) disable iff (!reset) $changed(count) |-> enable
    );

    // If count is 0 (excluding reset), the previous cycle must have been a wrap or hold.
    zero_implies_prev_zero_or_hold: assert property (
        @(posedge clk) disable iff (!reset) (count == 4'd0) |-> ($past(reset) && ($past(enable) || ($past(count) == 4'd0)))
    );

    // If count is 15 (excluding reset), the next cycle must wrap to 0 when enable is HIGH.
    wrap_on_max_when_enabled: assert property (
        @(posedge clk) disable iff (!reset) (count == 4'd15 && enable) |=> (count == 4'd0)
    );

    // With enable HIGH and count at 15, the next cycle must not increment further (wrap behavior).
    no_increment_past_max: assert property (
        @(posedge clk) disable iff (!reset) (count == 4'd15 && enable) |=> (count == 4'd0)
    );

    // With enable HIGH and count not at 15, the next cycle increments by 1.
    increment_no_wrap_when_enabled: assert property (
        @(posedge clk) disable iff (!reset) (count != 4'd15 && enable) |=> (count == $past(count) + 4'd1)
    );

    // With enable LOW and count not at 0, the next cycle holds its value.
    hold_no_wrap_when_disabled: assert property (
        @(posedge clk) disable iff (!reset) (count != 4'd0 && !enable) |=> (count == $past(count))
    );

    // With enable LOW and count at 0, the next cycle holds its value (no wrap on hold).
    hold_at_zero_when_disabled: assert property (
        @(posedge clk) disable iff (!reset) (count == 4'd0 && !enable) |=> (count == 4'd0)
    );
endmodule