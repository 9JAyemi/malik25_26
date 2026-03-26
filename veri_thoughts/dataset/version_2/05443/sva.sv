module loadable_downcounter8_sva (
    input logic countClock,
    input logic count,
    input logic [7:0] loadvalue,
    input logic load,
    input logic [7:0] countout
);

    // Next countout matches the RTL next-state function.
    check_next_state_matches_rtl: assert property (
        @(posedge countClock) disable iff (1'b0)
        1'b1 |=> countout == ($past(load) ? $past(loadvalue) : ($past(countout) - $past(count)))
    );

    // load causes countout to take loadvalue on the next clock.
    check_load_captures_value: assert property (
        @(posedge countClock) disable iff (1'b0)
        load |=> countout == $past(loadvalue)
    );

    // With load low and count low, countout holds its value.
    check_hold_when_idle: assert property (
        @(posedge countClock) disable iff (1'b0)
        !load && !count |=> countout == $past(countout)
    );

    // With load low and count high, countout decrements by one.
    check_decrement_when_count_high: assert property (
        @(posedge countClock) disable iff (1'b0)
        !load && count |=> countout == ($past(countout) - 8'd1)
    );

endmodule