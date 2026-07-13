module check_10us_sva (
    input logic clk,
    input logic start,
    input logic stop,
    input logic [31:0] elapsed_time,
    input logic [31:0] counter,     // internal reg from DUT
    input logic counting            // internal reg from DUT
);
    // Start sets counter to 0 on the next cycle.
    start_clears_counter: assert property (
        @(posedge clk) start |=> (counter == 32'd0)
    );

    // Start sets counting to 1 on the next cycle.
    start_sets_counting: assert property (
        @(posedge clk) start |=> (counting == 1'b1)
    );

    // Start does not update elapsed_time.
    start_does_not_update_elapsed: assert property (
        @(posedge clk) start |=> (elapsed_time == $past(elapsed_time))
    );

    // Stop (when start is low) clears counting on the next cycle.
    stop_clears_counting: assert property (
        @(posedge clk) (!start && stop) |=> (counting == 1'b0)
    );

    // Stop (when start is low) captures current counter into elapsed_time.
    stop_captures_counter: assert property (
        @(posedge clk) (!start && stop) |=> (elapsed_time == $past(counter))
    );

    // Stop (when start is low) does not change counter.
    stop_does_not_update_counter: assert property (
        @(posedge clk) (!start && stop) |=> (counter == $past(counter))
    );

    // While counting (and no start/stop), counter increments by 1.
    increment_while_counting: assert property (
        @(posedge clk) (counting && !start && !stop) |=> (counter == $past(counter) + 32'd1)
    );

    // While counting (and no start/stop), counting remains asserted.
    counting_sticky_high: assert property (
        @(posedge clk) (counting && !start && !stop) |=> (counting == 1'b1)
    );

    // When idle (no start/stop and not counting), all state holds.
    idle_state_stable: assert property (
        @(posedge clk) (!counting && !start && !stop) |=> ($stable(counter) && $stable(counting) && $stable(elapsed_time))
    );

    // If start and stop are both high, start takes priority: reset counter, set counting, keep elapsed_time.
    start_priority_over_stop: assert property (
        @(posedge clk) (start && stop) |=> (counter == 32'd0) && (counting == 1'b1) && (elapsed_time == $past(elapsed_time))
    );
endmodule