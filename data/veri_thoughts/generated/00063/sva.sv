module binary_counter_sva (
    input logic        clk,
    input logic        rst,
    input logic [15:0] max_count,
    input logic [15:0] count,
    input logic        done
);

    // Reset keeps count and done cleared.
    check_reset_clears_outputs: assert property (
        @(posedge clk) rst |-> (count == 16'd0 && done == 1'b0)
    );

    // Reaching max_count wraps count and raises done on the next cycle.
    check_wrap_on_max_count: assert property (
        @(posedge clk) disable iff (rst)
        (count == max_count) |=> (count == 16'd0 && done == 1'b1)
    );

    // Any non-max count increments and keeps done low on the next cycle.
    check_increment_when_not_max: assert property (
        @(posedge clk) disable iff (rst)
        (count != max_count) |=> (count == ($past(count) + 16'd1) && done == 1'b0)
    );

    // The first clock after reset release still observes the reset state.
    check_hold_reset_state_after_release: assert property (
        @(posedge clk) disable iff (rst)
        $past(rst) |-> (count == 16'd0 && done == 1'b0)
    );

    // done reflects whether the previous cycle hit max_count.
    check_done_reflects_previous_match: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) |-> (done == ($past(count) == $past(max_count)))
    );

endmodule