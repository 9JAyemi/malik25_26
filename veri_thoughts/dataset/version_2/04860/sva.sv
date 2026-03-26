module binary_counter_sva (
    input logic [3:0] count,
    input logic clk,
    input logic rst
);

    // Synchronous reset clears the counter.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'b0000)
    );

    // The first cycle after reset release still reflects the reset value.
    check_post_reset_count_zero: assert property (
        @(posedge clk) disable iff (rst) $past(rst) |-> (count == 4'b0000)
    );

    // On consecutive non-reset cycles, the counter increments by one.
    check_increment_every_cycle: assert property (
        @(posedge clk) disable iff (rst) !$past(rst) |-> (count == ($past(count) + 4'b0001))
    );

    // A maximum count value wraps back to zero on the next cycle.
    check_wrap_from_f_to_zero: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && ($past(count) == 4'b1111)) |-> (count == 4'b0000)
    );

endmodule