module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);
    // On a clock when reset is 1, count becomes 0 on the next clock.
    check_reset_clears_next: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // Reset has priority over enable if both are asserted.
    check_reset_dominates_enable: assert property (
        @(posedge clk) (reset && enable) |=> (count == 4'b0000)
    );

    // While reset stays asserted across cycles, count remains 0.
    check_reset_holds_zero: assert property (
        @(posedge clk) ($past(reset) && reset) |-> (count == 4'b0000)
    );

    // With enable deasserted (and not in reset), count holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) (!enable) |=> (count == $past(count))
    );

    // With enable asserted (and not in reset), count increments modulo 16.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset) (enable) |=> (count == ( $past(count) + 4'd1 )[3:0])
    );

    // Any change in count (excluding reset) implies prior cycle had enable high.
    check_change_implies_prev_enable: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && (count != $past(count))) |-> $past(enable)
    );

    // Without reset, next value must be either hold or +1 modulo 16.
    check_only_hold_or_increment: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> ((count == $past(count)) || (count == ( $past(count) + 4'd1 )[3:0]))
    );

    // When previous value was 4'hF and enable was 1 (no reset), wrap to 0.
    check_wrap_at_max: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && $past(enable) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // Two consecutive enables (no reset) produce +2 modulo 16 after two cycles.
    check_two_consecutive_enables_plus2: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset,1) && $past(!reset,2) && $past(enable,1) && $past(enable,2))
            |-> (count == ( $past(count,2) + 4'd2 )[3:0])
    );

    // Two consecutive disables (no reset) keep count equal to the value two cycles ago.
    check_two_consecutive_disables_hold: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset,1) && $past(!reset,2) && !$past(enable,1) && !$past(enable,2))
            |-> (count == $past(count,2))
    );
endmodule