module counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [7:0] count
);

    // Reset drives count to zero in the same cycle.
    reset_forces_zero: assert property (
        @(posedge clk) reset |-> (count == 8'h00)
    );

    // When not reset and enable is LOW, count holds its previous value.
    hold_when_disable: assert property (
        @(posedge clk) disable iff (reset) (!enable) |-> (count == $past(count))
    );

    // When not reset and enable is HIGH, count increments by 1.
    inc_when_enable: assert property (
        @(posedge clk) disable iff (reset) (enable) |-> (count == $past(count) + 8'd1)
    );

    // When not reset and enable is HIGH with previous count at 0xFF, wrap to 0x00.
    wrap_to_zero_on_255: assert property (
        @(posedge clk) disable iff (reset) (enable && ($past(count) == 8'hFF)) |-> (count == 8'h00)
    );

    // With enable HIGH for two consecutive non-reset cycles, count increases by 2 over two cycles.
    two_cycle_inc_on_enable_streak: assert property (
        @(posedge clk) disable iff (reset) (enable && $past(!reset && enable) && $past(1'b1,2)) |-> (count == $past(count,2) + 8'd2)
    );

    // After reset deasserts and enable is LOW, count remains at 0.
    hold_zero_after_reset_release: assert property (
        @(posedge clk) ($fell(reset) && (enable == 1'b0)) |-> (count == 8'h00)
    );

    // After reset deasserts and enable is HIGH, count becomes 1.
    one_after_reset_release_with_enable: assert property (
        @(posedge clk) ($fell(reset) && (enable == 1'b1)) |-> (count == 8'h01)
    );

    // When not reset, any change in count implies enable is HIGH.
    change_only_if_enable: assert property (
        @(posedge clk) disable iff (reset) (count != $past(count)) |-> (enable == 1'b1)
    );

    // With enable LOW for two consecutive non-reset cycles, count holds over two cycles.
    two_cycle_hold_when_disable_streak: assert property (
        @(posedge clk) disable iff (reset) (!enable && $past(!reset && !enable) && $past(1'b1,2)) |-> (count == $past(count,2))
    );

endmodule