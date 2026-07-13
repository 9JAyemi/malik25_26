module binary_counter_sva (
    input logic E,
    input logic s_aclk,
    input logic AR,
    input logic [3:0] Q
);

    // Q is zero on the cycle after an active reset.
    check_reset_clears_q: assert property (
        @(posedge s_aclk) disable iff ($initstate)
        $past(AR) |-> (Q == 4'b0000)
    );

    // Q holds its value when enable is low.
    check_hold_when_disabled: assert property (
        @(posedge s_aclk) disable iff ($initstate)
        !$past(AR) && !$past(E) |-> (Q == $past(Q))
    );

    // Q increments by one when enabled below 15.
    check_increment_when_enabled: assert property (
        @(posedge s_aclk) disable iff ($initstate)
        !$past(AR) && $past(E) && ($past(Q) != 4'b1111) |-> (Q == ($past(Q) + 4'b0001))
    );

    // Q wraps to zero when enabled at 15.
    check_wrap_from_max: assert property (
        @(posedge s_aclk) disable iff ($initstate)
        !$past(AR) && $past(E) && ($past(Q) == 4'b1111) |-> (Q == 4'b0000)
    );

endmodule