module counter_sva (
    input logic        clk,
    input logic        resetn,
    input logic [15:0] max_count,
    input logic [15:0] count,
    input logic        flag
);

    // Clock: clk
    // Active-low reset: resetn
    // Sequential counter with wrap flag

    // If reset stays low across clocks, both outputs stay cleared.
    check_reset_holds_outputs_cleared: assert property (
        @(posedge clk)
        (!resetn ##1 !resetn) |-> ((count == 16'd0) && (flag == 1'b0))
    );

    // Reaching max_count forces count back to zero on the next cycle.
    check_wrap_resets_count: assert property (
        @(posedge clk) disable iff (!resetn)
        (count == max_count) |=> (count == 16'd0)
    );

    // Reaching max_count raises flag on the next cycle.
    check_wrap_sets_flag: assert property (
        @(posedge clk) disable iff (!resetn)
        (count == max_count) |=> (flag == 1'b1)
    );

    // When not at max_count, count increments by one on the next cycle.
    check_non_wrap_increments_count: assert property (
        @(posedge clk) disable iff (!resetn)
        (count != max_count) |=> (count == ($past(count) + 16'd1))
    );

    // When not at max_count, flag is cleared on the next cycle.
    check_non_wrap_clears_flag: assert property (
        @(posedge clk) disable iff (!resetn)
        (count != max_count) |=> (flag == 1'b0)
    );

endmodule