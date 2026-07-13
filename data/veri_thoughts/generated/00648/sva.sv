module counter_sva (
    input logic clk,
    input logic rst,
    input logic enable,
    input logic load,
    input logic increment,
    input logic [7:0] data_in,
    input logic [7:0] count
);
    // After a cycle with rst=1, count must be 0 on the next cycle.
    check_reset_clears_on_next: assert property (
        @(posedge clk) disable iff (rst) $past(rst) |-> (count == 8'h00)
    );

    // While rst is asserted, the following cycle's count is 0 (synchronous reset).
    check_zero_during_reset: assert property (
        @(posedge clk) rst |=> (count == 8'h00)
    );

    // If load was 1 last cycle (and not in reset), count updates to data_in.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (rst) $past(load) && !$past(rst) |-> (count == $past(data_in))
    );

    // If enable&&increment last cycle with no load and not in reset, count increments by 1.
    check_increment_updates_count: assert property (
        @(posedge clk) disable iff (rst) !$past(load) && !$past(rst) && $past(enable && increment) |-> (count == $past(count) + 8'd1)
    );

    // If no load and no enable&&increment last cycle (and not in reset), count holds.
    check_stable_when_no_action: assert property (
        @(posedge clk) disable iff (rst) !$past(rst) && !$past(load) && !$past(enable && increment) |-> (count == $past(count))
    );

    // Increment at 8'hFF wraps to 8'h00 (no load, not in reset).
    check_increment_wraparound: assert property (
        @(posedge clk) disable iff (rst) !$past(rst) && !$past(load) && $past(enable && increment) && ($past(count) == 8'hFF) |-> (count == 8'h00)
    );

    // Load has priority over increment when both were asserted last cycle (not in reset).
    check_load_overrides_increment: assert property (
        @(posedge clk) disable iff (rst) !$past(rst) && $past(load) && $past(enable && increment) |-> (count == $past(data_in))
    );

    // Any change in count must be caused by rst, load, or (enable&&increment) last cycle.
    check_change_implies_cause: assert property (
        @(posedge clk) disable iff (rst) (count != $past(count)) |-> ($past(rst) || $past(load) || ($past(enable) && $past(increment)))
    );

    // If enable=1 and increment=0 last cycle with no load (and not in reset), count holds.
    check_enable_without_increment_no_change: assert property (
        @(posedge clk) disable iff (rst) !$past(rst) && !$past(load) && $past(enable) && !$past(increment) |-> (count == $past(count))
    );

    // If enable=0 and increment=1 last cycle with no load (and not in reset), count holds.
    check_increment_without_enable_no_change: assert property (
        @(posedge clk) disable iff (rst) !$past(rst) && !$past(load) && !$past(enable) && $past(increment) |-> (count == $past(count))
    );
endmodule