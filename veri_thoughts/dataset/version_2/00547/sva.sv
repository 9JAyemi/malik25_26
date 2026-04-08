module counter48_sva #(
    parameter DATASIZE = 16
) (
    input logic                 clk,
    input logic                 res_n,
    input logic                 increment,
    input logic [DATASIZE-1:0]  load,
    input logic                 load_enable,
    input logic [DATASIZE-1:0]  value
);

    // Reset holds the counter output at zero.
    check_reset_clears_value: assert property (
        @(posedge clk)
        (!$initstate && !res_n) |-> (value == {DATASIZE{1'b0}})
    );

    // A queued load updates value with the current load input on the next cycle.
    check_delayed_load_updates_value: assert property (
        @(posedge clk) disable iff (!res_n)
        (!$initstate && $past(res_n) && $past(load_enable)) |=> (value == $past(load))
    );

    // A queued load overrides increment.
    check_load_has_priority_over_increment: assert property (
        @(posedge clk) disable iff (!res_n)
        (!$initstate && $past(res_n) && $past(load_enable) && increment) |=> (value == $past(load))
    );

    // Without a queued load, increment advances the value by one.
    check_increment_advances_value: assert property (
        @(posedge clk) disable iff (!res_n)
        (!$initstate && $past(res_n) && !$past(load_enable) && increment) |=> (value == ($past(value) + 1'b1))
    );

    // Without a queued load or increment, the value holds.
    check_hold_without_activity: assert property (
        @(posedge clk) disable iff (!res_n)
        (!$initstate && $past(res_n) && !$past(load_enable) && !increment) |=> (value == $past(value))
    );

    // A new load_enable does not load immediately.
    check_load_enable_is_delayed: assert property (
        @(posedge clk) disable iff (!res_n)
        (!$initstate && $past(res_n) && !$past(load_enable) && load_enable && !increment) |=> (value == $past(value))
    );

    // A new load_enable does not block a same-cycle increment.
    check_increment_not_blocked_by_new_load_enable: assert property (
        @(posedge clk) disable iff (!res_n)
        (!$initstate && $past(res_n) && !$past(load_enable) && load_enable && increment) |=> (value == ($past(value) + 1'b1))
    );

endmodule