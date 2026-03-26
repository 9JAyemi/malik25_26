module counter_sva (
    input logic        clk,
    input logic        rst,
    input logic        ld,
    input logic [15:0] d,
    input logic [15:0] q,
    input logic        overflow
);

    // Synchronous reset clears q and overflow.
    check_reset_clears_state: assert property (
        @(posedge clk) rst |=> (q == 16'h0000 && overflow == 1'b0)
    );

    // Load captures d into q and clears overflow.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (rst)
        ld |=> (q == $past(d) && overflow == 1'b0)
    );

    // When not loading and not at max, q increments and overflow stays low.
    check_increment_behavior: assert property (
        @(posedge clk) disable iff (rst)
        (!ld && (q != 16'hFFFF)) |=> (q == ($past(q) + 16'h0001) && overflow == 1'b0)
    );

    // When not loading at max count, q wraps to zero and overflow is set.
    check_wrap_sets_overflow: assert property (
        @(posedge clk) disable iff (rst)
        (!ld && (q == 16'hFFFF)) |=> (q == 16'h0000 && overflow == 1'b1)
    );

    // A wrap-generated overflow pulse lasts only one cycle.
    check_overflow_single_cycle_on_wrap: assert property (
        @(posedge clk) disable iff (rst)
        (!ld && (q == 16'hFFFF)) |=> (overflow == 1'b1) ##1 (overflow == 1'b0)
    );

endmodule