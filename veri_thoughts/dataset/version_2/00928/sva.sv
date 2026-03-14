module synchronizer_sva (
    input logic clk,
    input logic rst,
    input logic x,
    input logic sync_x
);
    // Clock: clk posedge. Reset: rst active-high, asynchronous. Sequential 2-FF sync; sync_x is the second flop.

    // When reset is seen HIGH at a clock edge, sync_x is LOW on the next clock.
    check_sync_clears_one_cycle_after_reset_seen: assert property (
        @(posedge clk) rst |=> (sync_x == 1'b0)
    );

    // While reset is held HIGH across consecutive clocks, sync_x must be LOW.
    check_sync_low_while_reset_held: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (sync_x == 1'b0)
    );

    // Immediately after reset deasserts at a clock edge, sync_x remains LOW.
    check_sync_low_on_reset_fall: assert property (
        @(posedge clk) $fell(rst) |-> (sync_x == 1'b0)
    );

    // If reset was HIGH in the previous cycle, sync_x must be LOW now.
    check_sync_low_if_prev_reset: assert property (
        @(posedge clk) $past(rst) |-> (sync_x == 1'b0)
    );

    // Changes on x during held reset cannot affect sync_x; it stays LOW.
    check_input_ignored_during_reset: assert property (
        @(posedge clk) (rst && $past(rst) && (x != $past(x))) |-> (sync_x == 1'b0)
    );
endmodule