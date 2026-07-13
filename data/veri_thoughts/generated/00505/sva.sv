module sync_counter_sva(
    input logic clk,
    input logic reset_n,
    input logic enable,
    input logic [3:0] count
);

    // Active-low reset clears the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !reset_n |-> (count == 4'b0000)
    );

    // When enabled, the counter increments by one on the next clock.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (!reset_n)
        enable |=> (count == ($past(count) + 4'd1))
    );

    // When not enabled, the counter holds its value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (!reset_n)
        !enable |=> (count == $past(count))
    );

    // When enabled at its maximum value, the counter wraps to zero.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (!reset_n)
        (enable && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule