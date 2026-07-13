module binary_counter_sva (
    input logic E,
    input logic s_aclk,
    input logic AR,
    input logic [3:0] Q
);
    // Clock: s_aclk (posedge). Reset: AR (synchronous, active-high). Sequential counter with wrap at 15.

    // AR high forces Q to 0 on the next cycle.
    reset_sets_zero_next: assert property (
        @(posedge s_aclk) AR |=> (Q == 4'b0000)
    );

    // When E is high and Q is not 15, Q increments by 1 on the next cycle.
    increment_when_enabled_not_max: assert property (
        @(posedge s_aclk) disable iff (AR) (E && (Q != 4'hF)) |=> (Q == $past(Q) + 4'd1)
    );

    // When E is high and Q is 15, Q wraps to 0 on the next cycle.
    wrap_when_enabled_at_max: assert property (
        @(posedge s_aclk) disable iff (AR) (E && (Q == 4'hF)) |=> (Q == 4'h0)
    );

    // When E is low, Q holds its value on the next cycle.
    hold_when_disabled: assert property (
        @(posedge s_aclk) disable iff (AR) (!E) |=> (Q == $past(Q))
    );

    // Any change in Q must be caused by AR or E in the previous cycle.
    change_requires_enable_or_reset: assert property (
        @(posedge s_aclk) disable iff (AR) (Q != $past(Q)) |-> ($past(AR) || $past(E))
    );

    // If E and Q are not 15 in the same cycle, Q must change on the next cycle.
    enable_changes_when_not_max: assert property (
        @(posedge s_aclk) disable iff (AR) (E && (Q != 4'hF)) |=> (Q != $past(Q))
    );

    // If E and Q are 15 in the same cycle, Q must wrap to 0 on the next cycle.
    enable_wraps_when_max: assert property (
        @(posedge s_aclk) disable iff (AR) (E && (Q == 4'hF)) |=> (Q == 4'h0)
    );

    // If AR and E are both high in the same cycle, AR has priority and Q becomes 0 on the next cycle.
    reset_priority_over_enable: assert property (
        @(posedge s_aclk) (AR && E) |=> (Q == 4'h0)
    );

    // If E is high and Q is not 15, Q must change on the next cycle.
    increment_changes_when_not_max: assert property (
        @(posedge s_aclk) disable iff (AR) (E && (Q != 4'hF)) |=> (Q != $past(Q))
    );

    // If E is high and Q is 15, Q must change on the next cycle (wrap to 0).
    wrap_changes_when_max: assert property (
        @(posedge s_aclk) disable iff (AR) (E && (Q == 4'hF)) |=> (Q != $past(Q))
    );

endmodule