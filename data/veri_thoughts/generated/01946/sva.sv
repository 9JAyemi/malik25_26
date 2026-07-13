module counter_sva (
    input logic clk,
    input logic rst,
    input logic up_down,
    input logic enable,
    input logic [3:0] count
);
    // Clock: clk (posedge). Reset: rst (synchronous, active-high). Logic: sequential up/down counter.

    // Reset drives count to zero on the following clock.
    reset_clears_next: assert property (
        @(posedge clk) rst |=> (count == 4'd0)
    );

    // While reset stays asserted across cycles, count remains zero.
    hold_zero_while_reset: assert property (
        @(posedge clk) rst && $past(rst,1,1'b0) |-> (count == 4'd0)
    );

    // With enable=0 (not in reset), count holds its value to the next cycle.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst) (!enable) |=> $stable(count)
    );

    // With enable=1 and up_down=1, count increments by 1 modulo 16 on next cycle.
    increment_when_up: assert property (
        @(posedge clk) disable iff (rst) (enable && up_down) |=> (count == (($past(count,1,4'd0) + 4'd1) & 4'hF))
    );

    // With enable=1 and up_down=0, count decrements by 1 modulo 16 on next cycle.
    decrement_when_down: assert property (
        @(posedge clk) disable iff (rst) (enable && !up_down) |=> (count == (($past(count,1,4'd0) - 4'd1) & 4'hF))
    );

    // With enable=1 (not in reset), count must change on the next cycle.
    change_when_enabled: assert property (
        @(posedge clk) disable iff (rst) (enable) |=> !$stable(count)
    );

    // If count changes (not in reset), enable must have been 1 in the previous cycle.
    change_implies_enable_prev: assert property (
        @(posedge clk) disable iff (rst) (count != $past(count,1,4'd0)) |-> $past(enable,1,1'b0)
    );

    // With enable=1, next value is either +1 or -1 modulo 16.
    next_is_pm1_when_enabled: assert property (
        @(posedge clk) disable iff (rst) (enable) |=> (
            (count == (($past(count,1,4'd0) + 4'd1) & 4'hF)) ||
            (count == (($past(count,1,4'd0) - 4'd1) & 4'hF))
        )
    );

endmodule