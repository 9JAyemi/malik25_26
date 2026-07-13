module counter_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic [3:0] data_in,
    input logic [3:0] count
);

    // Assume reset is asserted in the initial cycle to make $past well-defined.
    assume_initial_reset: assume property (
        @(posedge clk) $initstate |-> reset
    );

    // Synchronous reset drives count to 0 on the next clock.
    reset_forces_zero: assert property (
        @(posedge clk) reset |=> (count == 4'd0)
    );

    // When not in reset, load updates count with data_in on the next clock.
    load_updates_count: assert property (
        @(posedge clk) disable iff (reset) load |=> (count == $past(data_in))
    );

    // When not in reset and not loading, count increments by 1 (mod-16) on the next clock.
    incr_when_no_load: assert property (
        @(posedge clk) disable iff (reset) !load |=> (count == ($past(count) + 4'd1))
    );

    // When previous cycle was not reset and no load, count wraps from 15 to 0.
    wrap_on_max: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && !$past(load) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // If reset stays asserted across back-to-back clocks, count remains 0.
    hold_zero_while_reset: assert property (
        @(posedge clk) ($past(reset) && reset) |-> (count == 4'd0)
    );

    // When previous cycle was not in reset, current count matches last-cycle load/inc choice.
    next_state_match: assert property (
        @(posedge clk) disable iff (reset) !$past(reset) |-> (count == ($past(load) ? $past(data_in) : ($past(count) + 4'd1)))
    );

endmodule