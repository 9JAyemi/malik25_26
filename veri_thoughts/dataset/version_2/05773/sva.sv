module counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    // While reset is asserted, count must be zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) reset |-> (count == 4'b0000)
    );

    // A reset in the previous cycle clears count to zero.
    check_prev_reset_clears_count: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(reset)) |-> (count == 4'b0000)
    );

    // When enabled, count increments by one on the next cycle.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset) && $past(enable)) |-> (count == ($past(count) + 4'd1))
    );

    // When not enabled, count holds its value on the next cycle.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset) && !$past(enable)) |-> (count == $past(count))
    );

endmodule