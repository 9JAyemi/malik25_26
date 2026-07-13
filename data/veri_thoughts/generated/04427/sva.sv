module synchronous_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    // Synchronous active-high reset clears the counter.
    check_reset_clears_count: assert property (
        @(posedge clk)
        reset |=> (count == 4'b0000)
    );

    // When enabled below 15, the counter increments by one.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count != 4'hF) |=> (count == ($past(count) + 4'd1))
    );

    // When enabled at 15, the counter wraps to zero.
    check_enable_wraps_count: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count == 4'hF) |=> (count == 4'h0)
    );

    // When not enabled, the counter holds its value.
    check_disable_holds_count: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (count == $past(count))
    );

endmodule