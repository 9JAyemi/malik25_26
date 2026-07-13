module Counter_sva (
    input logic clk,
    input logic reset,          // active-low reset
    input logic count_en,
    input logic [31:0] max_count,
    input logic [31:0] count
);
    ///// Reset behavior /////
    // While reset is asserted (low), count must be 0.
    reset_drives_zero: assert property (
        @(posedge clk) !reset |-> (count == 32'd0)
    );
    // On reset deassertion edge, count is 0 in that cycle.
    zero_on_reset_release: assert property (
        @(posedge clk) $rose(reset) |-> (count == 32'd0)
    );
    // If reset stays low across cycles, count remains stable at 0.
    stable_while_reset_held: assert property (
        @(posedge clk) (!reset && $past(!reset)) |-> (count == $past(count))
    );

    ///// Counting behavior /////
    // When disabled, the counter holds its value.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (!reset)
            (!count_en) |=> (count == $past(count))
    );
    // When enabled, next value is +1 unless at max_count, then it wraps to 0.
    update_when_enabled: assert property (
        @(posedge clk) disable iff (!reset)
            (count_en) |=> (count == (($past(count) == $past(max_count)) ? 32'd0 : ($past(count) + 32'd1)))
    );
    // Any change between cycles (out of reset) requires enable in the previous cycle.
    change_requires_enable: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset) && (count != $past(count))) |-> $past(count_en)
    );
    // If enabled at all-ones and not equal to max_count, next value wraps to 0 via +1 overflow.
    overflow_wrap_to_zero: assert property (
        @(posedge clk) disable iff (!reset)
            (count_en && (count == 32'hFFFF_FFFF) && (count != max_count)) |=> (count == 32'd0)
    );
    // If next value is 0 with enable high previously, cause is wrap-to-zero or max_count match.
    enabled_zero_next_cycle_has_cause: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset) && $past(count_en) && (count == 32'd0)) |-> (($past(count) == $past(max_count)) || ($past(count) == 32'hFFFF_FFFF))
    );
endmodule