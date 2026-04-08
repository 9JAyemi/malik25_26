module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic       en,
    input logic [1:0] count
);

    // Reset drives count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 2'b00)
    );

    // Reset has priority even when enable is high.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (rst && en) |=> (count == 2'b00)
    );

    // Enable increments the counter by one.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff (rst) en |=> (count == ($past(count) + 2'b01))
    );

    // Disable holds the counter value.
    check_disable_holds_count: assert property (
        @(posedge clk) disable iff (rst) !en |=> (count == $past(count))
    );

    // The maximum count wraps to zero when enabled.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (rst) (en && (count == 2'b11)) |=> (count == 2'b00)
    );

endmodule