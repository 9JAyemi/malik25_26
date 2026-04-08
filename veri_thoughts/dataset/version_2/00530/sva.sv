module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic       en,
    input logic [3:0] count
);

    // Synchronous reset clears the counter on the next cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'd0)
    );

    // Reset has priority over enable and still clears the counter.
    check_reset_overrides_enable: assert property (
        @(posedge clk) (rst && en) |=> (count == 4'd0)
    );

    // When enabled outside reset, the counter increments by one.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff (rst) en |=> (count == ($past(count) + 4'd1))
    );

    // When not enabled outside reset, the counter holds its value.
    check_disable_holds_count: assert property (
        @(posedge clk) disable iff (rst) !en |=> (count == $past(count))
    );

    // A 4-bit maximum value wraps to zero when incremented.
    check_wraps_after_max: assert property (
        @(posedge clk) disable iff (rst) (en && (count == 4'hf)) |=> (count == 4'h0)
    );

endmodule