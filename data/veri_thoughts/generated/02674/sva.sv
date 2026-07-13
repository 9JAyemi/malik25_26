module clock_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);
    // When rst is HIGH, count is driven to 0.
    reset_forces_zero: assert property (
        @(posedge clk) rst |-> (count == 4'd0)
    );

    // While rst remains HIGH across cycles, count does not change.
    reset_holds_value_stable: assert property (
        @(posedge clk) ($past(rst) && rst) |-> $stable(count)
    );

    // When not in reset in consecutive cycles, count increments by 1.
    count_increments_by_one: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) |-> (count == ($past(count) + 4'd1))
    );

    // When previous count was 0xF without reset, it wraps to 0x0.
    wrap_from_f_to_0: assert property (
        @(posedge clk) disable iff (rst) ($past(!rst) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // If current count is 0 without reset previously, last count was 0xF (wrap only).
    zero_only_after_wrap: assert property (
        @(posedge clk) disable iff (rst) ($past(!rst) && (count == 4'h0)) |-> ($past(count) == 4'hF)
    );

    // On reset deassertion, count becomes 1 on that cycle.
    first_cycle_after_reset_is_one: assert property (
        @(posedge clk) $fell(rst) |-> (count == 4'd1)
    );

    // Without reset in consecutive cycles, count must change every cycle.
    no_hold_without_reset: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) |-> (count != $past(count))
    );

    // With two consecutive non-reset cycles, count advances by 2.
    two_cycle_increment_by_two: assert property (
        @(posedge clk) disable iff (rst) ($past(!rst,1) && $past(!rst,2)) |-> (count == ($past(count,2) + 4'd2))
    );

    // With three consecutive non-reset cycles, count advances by 3.
    three_cycle_increment_by_three: assert property (
        @(posedge clk) disable iff (rst) ($past(!rst,1) && $past(!rst,2) && $past(!rst,3)) |-> (count == ($past(count,3) + 4'd3))
    );
endmodule