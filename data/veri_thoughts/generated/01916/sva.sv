module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // If EN was 1 on the previous edge, ENCLK now equals previous TE (1-cycle capture).
    check_capture_on_prev_enable: assert property (
        @(posedge CLK) $past(EN) |-> (ENCLK == $past(TE))
    );

    // If EN was 0 on the previous edge, ENCLK holds its value.
    check_hold_on_prev_disable: assert property (
        @(posedge CLK) $past(!EN) |-> (ENCLK == $past(ENCLK))
    );

    // Any change in ENCLK implies EN was 1 in the prior cycle.
    check_change_requires_enable: assert property (
        @(posedge CLK) (ENCLK != $past(ENCLK)) |-> $past(EN)
    );

    // When ENCLK changes, the new value must equal TE from the prior cycle.
    check_changed_value_matches_prev_te: assert property (
        @(posedge CLK) (ENCLK != $past(ENCLK)) |-> (ENCLK == $past(TE))
    );

    // TE changes have no effect when EN was 0 in the prior cycle.
    check_te_change_ignored_when_prev_disabled: assert property (
        @(posedge CLK) ($past(!EN) && (TE != $past(TE))) |-> (ENCLK == $past(ENCLK))
    );

    // If EN was 1 and TE did not change since last edge, ENCLK equals TE now.
    check_match_when_prev_enabled_and_te_stable: assert property (
        @(posedge CLK) ($past(EN) && (TE == $past(TE))) |-> (ENCLK == TE)
    );

    // If EN was 0 and is still 0, ENCLK must not change at this edge.
    check_no_change_across_two_cycle_disable: assert property (
        @(posedge CLK) ($past(!EN) && !EN) |-> (ENCLK == $past(ENCLK))
    );

    // If EN was 1 and TE changed at the current edge, ENCLK still reflects the prior TE (1-cycle latency).
    check_latency_when_prev_enabled_te_changed_now: assert property (
        @(posedge CLK) ($past(EN) && (TE != $past(TE))) |-> (ENCLK == $past(TE))
    );
endmodule