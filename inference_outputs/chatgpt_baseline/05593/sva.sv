module binary_counter_sva(
    input logic       E,
    input logic       s_aclk,
    input logic       AR,
    input logic [3:0] Q
);

    // Reset drives the counter to zero on the next sampled cycle.
    check_reset_clears_q: assert property (
        @(posedge s_aclk)
        !$initstate && $past(AR) |-> (Q == 4'b0000)
    );

    // Counter holds its value when enable is low and reset is not active.
    check_hold_when_disabled: assert property (
        @(posedge s_aclk) disable iff (AR)
        !$initstate && $past(!AR && !E) |-> (Q == $past(Q))
    );

    // Counter increments by one when enabled below 4'hF.
    check_increment_when_enabled: assert property (
        @(posedge s_aclk) disable iff (AR)
        !$initstate && $past(!AR && E) && ($past(Q) != 4'hF) |-> (Q == ($past(Q) + 4'd1))
    );

    // Counter wraps to zero when enabled at 4'hF.
    check_wrap_from_max: assert property (
        @(posedge s_aclk) disable iff (AR)
        !$initstate && $past(!AR && E) && ($past(Q) == 4'hF) |-> (Q == 4'b0000)
    );

    // Q only changes after a reset or an enabled count.
    check_q_changes_only_on_reset_or_enable: assert property (
        @(posedge s_aclk) disable iff (AR)
        !$initstate && (Q != $past(Q)) |-> $past(AR || E)
    );

endmodule