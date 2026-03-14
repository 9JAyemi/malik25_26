module binary_counter_sva (
    input logic clk,
    input logic rst,          // active-low reset
    input logic [3:0] count
);
    // When reset is asserted (low), count must be 0 at each clock edge.
    check_reset_forces_zero: assert property (
        @(posedge clk) (!rst) |-> (count == 4'h0)
    );

    // While reset stays asserted across cycles, count remains 0 and stable.
    check_hold_zero_during_reset: assert property (
        @(posedge clk) (!rst && !$past(rst)) |-> (count == 4'h0 && $stable(count))
    );

    // With reset deasserted in consecutive cycles, count increments by 1 each cycle (mod 16).
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> (count == $past(count) + 4'd1)
    );

    // When previous value was 15 and still enabled, next value wraps to 0.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // Over two consecutive enabled cycles, count advances by 2 (mod 16).
    check_two_step_increment: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst,2) && $past(rst)) |-> (count == $past(count,2) + 4'd2)
    );

    // On reset release ($rose), the next enabled cycle increments from the reset value.
    check_increment_after_reset_release: assert property (
        @(posedge clk) disable iff (!rst) $rose(rst) |-> (count == $past(count) + 4'd1)
    );

    // On reset assertion ($fell), count is driven to 0 at that clock edge.
    check_zero_on_reset_assertion: assert property (
        @(posedge clk) $fell(rst) |-> (count == 4'h0)
    );

    // When enabled and not wrapping, next value cannot be 0.
    check_nonzero_when_not_wrapping: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && ($past(count) != 4'hF)) |-> (count != 4'h0)
    );
endmodule