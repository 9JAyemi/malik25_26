// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_enclk_is_gated_clk, assert, property, check_enclk_low_when_te_low, check_enclk_high_when_te_high, check_en_rise_propagates_to_enclk, rose, check_en_fall_propagates_to_enclk, fell, check_d_rise_propagates_to_q, check_d_fall_propagates_to_q, check_q_rise_requires_enclk, past, check_q_fall_requires_enclk, check_en_rise_propagates_to_q, check_en_fall_propagates_to_q
bind DFFE d_ff_en_gate_sva auto_sva_inst (
    .CLK(CLK),
    .D(D),
    .EN(EN),
    .TE(TE),
    .Q(Q),
    .ENCLK(ENCLK),
    .posedge(posedge)
);
