// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_enclk_matches_te, assert, property, disable, iff, b0, check_enclk_rises_on_te_rise, rose, check_enclk_falls_on_te_fall, fell, check_enclk_holds_when_te_high, past, check_enclk_holds_when_te_low, check_q_captures_d_on_en_rise, check_q_holds_on_en_fall, check_q_captures_d_on_enclk_rise, check_q_holds_on_enclk_fall
bind DFFE d_ff_en_gate_sva auto_sva_inst (
    .CLK(CLK),
    .D(D),
    .EN(EN),
    .TE(TE),
    .Q(Q),
    .ENCLK(ENCLK),
    .posedge(posedge)
);
