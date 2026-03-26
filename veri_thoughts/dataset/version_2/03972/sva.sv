module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    // Reset clears the counter on the following clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'd0)
    );

    // With reset low, enable increments count by one modulo 16.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (count == ($past(count) + 4'd1))
    );

    // With reset low and enable low, the counter holds its value.
    check_disable_holds_count: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (count == $past(count))
    );

endmodule