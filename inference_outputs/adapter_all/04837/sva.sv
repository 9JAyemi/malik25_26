module counter_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [1:0] count
);
    // Clock: clk (posedge). Reset: rst (active-low, asynchronous). Sequential counter with enable.

    // When reset is asserted low, count must be 0.
    reset_forces_zero: assert property (
        @(posedge clk) (rst == 1'b0) |-> (count == 2'b00)
    );

    // When enabled and not at max, count increments by 1.
    count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (!rst) (en && (count != 2'b11)) |=> (count == $past(count) + 2'b01)
    );

    // When enabled and at max, count wraps to 0.
    count_wraps_when_enabled_at_max: assert property (
        @(posedge clk) disable iff (!rst) (en && (count == 2'b11)) |=> (count == 2'b00)
    );

    // When disabled, count holds its value.
    count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (!rst) (!en) |=> (count == $past(count))
    );

    // Any change in count must be caused by reset or an enabled cycle.
    count_change_requires_enable_or_reset: assert property (
        @(posedge clk) disable iff (!rst) (count != $past(count)) |-> ($past(rst) == 1'b0 || $past(en) == 1'b1)
    );

    // If reset was low on the previous cycle, count must be 0 now.
    prev_reset_low_implies_count_zero: assert property (
        @(posedge clk) $past(rst) == 1'b0 |-> (count == 2'b00)
    );

    // If reset was high and enabled last cycle, count must change now.
    prev_reset_high_and_enabled_implies_change: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && $past(en)) |-> (count != $past(count))
    );

    // If reset was high and disabled last cycle, count must hold now.
    prev_reset_high_and_disabled_implies_hold: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && !$past(en)) |-> (count == $past(count))
    );

    // If count is 0 now, it must have come from 1 or wrapped from 3 last cycle.
    zero_now_has_valid_prev: assert property (
        @(posedge clk) disable iff (!rst) (count == 2'b00) |-> (($past(count) == 2'b01) || ($past(count) == 2'b11))
    );

    // If count is 1 now, it must have come from 0 or incremented from 2 last cycle.
    one_now_has_valid_prev: assert property (
        @(posedge clk) disable iff (!rst) (count == 2'b01) |-> (($past(count) == 2'b00) || ($past(count) == 2'b10))
    );

    // If count is 2 now, it must have come from 1 last cycle.
    two_now_has_valid_prev: assert property (
        @(posedge clk) disable iff (!rst) (count == 2'b10) |-> ($past(count) == 2'b01)
    );

    // If count is 3 now, it must have come from 2 last cycle.
    three_now_has_valid_prev: assert property (
        @(posedge clk) disable iff (!rst) (count == 2'b11) |-> ($past(count) == 2'b10)
    );
endmodule