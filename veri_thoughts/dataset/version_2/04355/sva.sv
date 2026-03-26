module counter_sva (
    input logic        clk,
    input logic        rst,
    input logic        en,
    input logic [31:0] count_to,
    input logic [31:0] count
);

    // On the first cycle after reset, count is zero.
    check_count_zero_after_reset_cycle: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && $past(rst)) |-> (count == 32'd0)
    );

    // When enable is low, count holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst)
        (!en) |=> (count == $past(count))
    );

    // When enabled below count_to, count increments by one.
    check_increment_when_enabled_below_limit: assert property (
        @(posedge clk) disable iff (rst)
        (en && (count != count_to)) |=> (count == ($past(count) + 32'd1))
    );

    // When enabled at count_to, count wraps to zero.
    check_wrap_to_zero_at_limit: assert property (
        @(posedge clk) disable iff (rst)
        (en && (count == count_to)) |=> (count == 32'd0)
    );

    // Any non-reset count change must come from an enabled prior cycle.
    check_change_requires_enable: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && !$past(rst) && (count != $past(count))) |-> $past(en)
    );

    // Every non-reset transition follows the RTL update rules.
    check_nonreset_transition_matches_rtl: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && !$past(rst)) |-> (
            ((!$past(en)) && (count == $past(count))) ||
            ($past(en) && ($past(count) == $past(count_to)) && (count == 32'd0)) ||
            ($past(en) && ($past(count) != $past(count_to)) && (count == ($past(count) + 32'd1)))
        )
    );

endmodule