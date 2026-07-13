module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);
    ///// Counter behavior /////
    // Synchronous reset drives count to 0.
    check_reset_clears_to_zero: assert property (
        @(posedge clk) reset |-> (count == 4'd0)
    );

    // When enable was LOW, hold the previous count.
    check_hold_when_enable_low: assert property (
        @(posedge clk) disable iff (reset) !$past(enable) |-> (count == $past(count))
    );

    // With enable HIGH and previous count not 15, increment by 1.
    check_increment_on_enable: assert property (
        @(posedge clk) disable iff (reset) $past(enable) && !$past(reset) && ($past(count) != 4'd15) |-> (count == $past(count) + 4'd1)
    );

    // With enable HIGH and previous count 15, wrap to 0.
    check_wrap_on_max: assert property (
        @(posedge clk) disable iff (reset) $past(enable) && !$past(reset) && ($past(count) == 4'd15) |-> (count == 4'd0)
    );

    // If count changed without current reset, prior enable must have been HIGH or prior reset was HIGH.
    check_change_requires_enable_or_prev_reset: assert property (
        @(posedge clk) disable iff (reset) (count != $past(count)) |-> ($past(enable) || $past(reset))
    );

    // Without prior reset, next count equals the RTL next-state function.
    check_next_state_function: assert property (
        @(posedge clk) disable iff (reset)
            !$past(reset) |-> (count == ($past(enable) ? (($past(count) == 4'd15) ? 4'd0 : ($past(count) + 4'd1)) : $past(count)))
    );

    // Without prior reset, reaching 0 with enable implies previous value was 15.
    check_zero_only_from_wrap_when_enabled: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && (count == 4'd0) && $past(enable)) |-> ($past(count) == 4'd15)
    );
endmodule