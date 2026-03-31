module bin_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);

    // Reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 4'h0)
    );

    // When enable is low, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (count == $past(count))
    );

    // When enable is high, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (count == ($past(count) + 4'd1))
    );

    // The counter value never exceeds the previous value plus one.
    check_count_monotonic: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (count >= $past(count))
    );

endmodule