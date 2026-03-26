module binary_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic       en,
    input logic [3:0] count
);

    // Reset clears the counter.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'b0000)
    );

    // Enable increments the counter by one modulo 16.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (rst) en |=> (count == ($past(count) + 4'd1))
    );

    // When not enabled, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst) !en |=> (count == $past(count))
    );

    // Reset has priority even if enable is also high.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (rst && en) |=> (count == 4'b0000)
    );

endmodule