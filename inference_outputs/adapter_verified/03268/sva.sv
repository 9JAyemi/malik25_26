module binary_counter_sva (
    input logic clk,
    input logic [3:0] reset,
    input logic [3:0] enable,
    input logic [3:0] count
);

// Reset drives count to zero on the next cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

// With enable high, count increments by one on the next cycle.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (reset) enable |=> (count == ($past(count) + 4'd1))
    );

// With enable low, count holds its value on the next cycle.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |=> (count == $past(count))
    );

// Incrementing from 4'hF wraps count back to 4'h0.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset) (enable && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule
