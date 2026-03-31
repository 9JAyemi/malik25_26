module counter_sva (
    input logic clk,
    input logic rst,
    input logic enable,
    input logic [31:0] count
);
    // Clock: clk (posedge). Reset: rst (active-high, synchronous).
    // Sequential logic: posedge clocked counter with enable.
    // Behavior: rst -> count=0; else if enable -> count=count+1; else hold.

    // When rst is high at the clock edge, count is driven to 0.
    reset_clears_count: assert property (
        @(posedge clk) rst |-> (count == 32'd0)
    );

    // Outside reset, next-state equals previous plus (enable ? 1 : 0).
    next_state_function: assert property (
        @(posedge clk) disable iff (rst) (!$initstate) |-> (count == $past(count) + (enable ? 32'd1 : 32'd0))
    );

    // Outside reset, if count changes, enable must be 1.
    change_implies_enable: assert property (
        @(posedge clk) disable iff (rst) (!$initstate && (count != $past(count))) |-> enable
    );

    // Outside reset, if enable is 1, count must change.
    enable_implies_change: assert property (
        @(posedge clk) disable iff (rst) (!$initstate && enable) |-> (count != $past(count))
    );

    // While rst is held high across cycles, count stays 0.
    reset_holds_zero: assert property (
        @(posedge clk) (!$initstate && rst && $past(rst)) |-> (count == 32'd0) && ($past(count) == 32'd0)
    );

    // On the first cycle after reset deasserts with enable=0, count remains 0.
    post_reset_zero_if_disabled: assert property (
        @(posedge clk) (!$initstate && $past(rst) && !rst && !enable) |-> (count == 32'd0)
    );

    // On the first cycle after reset deasserts with enable=1, count becomes 1.
    post_reset_one_if_enabled: assert property (
        @(posedge clk) (!$initstate && $past(rst) && !rst && enable) |-> (count == 32'd1)
    );
endmodule