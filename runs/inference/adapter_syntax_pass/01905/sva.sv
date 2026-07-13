module simple_counter_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [31:0] count
);

    // Reset clears the counter on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 32'd0)
    );

    // Reset has priority over enable.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (rst && en) |=> (count == 32'd0)
    );

    // Enable increments the counter by one.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff (rst) en |=> (count == ($past(count) + 32'd1))
    );

    // Disable holds the counter value.
    check_disable_holds_count: assert property (
        @(posedge clk) disable iff (rst) !en |=> (count == $past(count))
    );

endmodule