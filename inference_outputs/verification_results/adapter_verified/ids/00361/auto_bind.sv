// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_enclk_is_gated_clk, assert, property, check_q_holds_when_en_low, past, check_q_captures_d_when_en_high, check_q_updates_on_d_change_when_en_high, check_q_stable_when_en_high_and_d_equals_q
bind DFFE d_ff_en_gate_sva auto_sva_inst (
    .CLK(CLK),
    .D(D),
    .EN(EN),
    .TE(TE),
    .Q(Q),
    .ENCLK(ENCLK),
    .posedge(posedge)
);
