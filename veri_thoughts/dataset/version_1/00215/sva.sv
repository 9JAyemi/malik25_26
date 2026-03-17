module up_down_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       up,
    input logic       down,
    input logic [2:0] count
);

    // Count is zero whenever reset is active.
    check_reset_holds_zero: assert property (
        @(posedge clk)
        !$initstate && reset |-> (count == 3'b000)
    );

    // Count holds when neither up nor down was asserted.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && $past(!reset && !up && !down) |-> (count == $past(count))
    );

    // Count increments on up below 7, regardless of down.
    check_up_increments: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && $past(!reset && up) && ($past(count) != 3'b111)
        |-> (count == ($past(count) + 3'b001))
    );

    // Count wraps to zero on up from 7, regardless of down.
    check_up_wraps_to_zero: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && $past(!reset && up) && ($past(count) == 3'b111)
        |-> (count == 3'b000)
    );

    // Count decrements on down only when up was low.
    check_down_decrements: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && $past(!reset && !up && down) && ($past(count) != 3'b000)
        |-> (count == ($past(count) - 3'b001))
    );

    // Count wraps to 7 on down from 0 when up was low.
    check_down_wraps_to_max: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && $past(!reset && !up && down) && ($past(count) == 3'b000)
        |-> (count == 3'b111)
    );

endmodule