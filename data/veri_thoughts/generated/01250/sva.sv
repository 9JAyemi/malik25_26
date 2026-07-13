module timebase_sva #(
    parameter integer n = 12,
    parameter integer value = 0
) (
    input logic clock,
    input logic reset,
    input logic enable,
    input logic tick,
    input logic [n-1:0] count_value
);

    ///// Reset behavior /////
    // While reset is HIGH, outputs are forced: tick=0 and count_value=value.
    check_reset_drives_outputs: assert property (
        @(posedge clock) reset |-> (tick == 1'b0) && (count_value == value)
    );

    ///// Tick behavior /////
    // When not in reset, tick equals enable (combinational function of inputs at the edge).
    check_tick_matches_enable_when_not_reset: assert property (
        @(posedge clock) disable iff (reset) tick == enable
    );

    // If tick is HIGH, reset must be LOW and enable must be HIGH.
    check_tick_requires_enable_and_no_reset: assert property (
        @(posedge clock) tick |-> (!reset && enable)
    );

    // If enable is HIGH with reset LOW, tick must be HIGH in the same cycle.
    check_enable_sets_tick: assert property (
        @(posedge clock) disable iff (reset) enable |-> (tick == 1'b1)
    );

    // If enable is LOW with reset LOW, tick must be LOW in the same cycle.
    check_disable_clears_tick: assert property (
        @(posedge clock) disable iff (reset) (!enable) |-> (tick == 1'b0)
    );

endmodule