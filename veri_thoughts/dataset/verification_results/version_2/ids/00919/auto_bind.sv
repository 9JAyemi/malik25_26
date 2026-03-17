// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): past_valid, always_ff, reset_waveform_matches_select, assert, property, hFF, h00, after_reset_deassert_first_step, disable, iff, fell, d254, d1, inc_when_select0_stable, past, dec_when_select1_stable, d255, toggle_1to0_sum_256, h100, toggle_0to1_sum_254, rose, h0FE, wrap_inc_ff_to_00, wrap_dec_00_to_ff
bind up_counter triangular_waveform_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .select(select),
    .waveform(waveform),
    .posedge(posedge),
    .begin(begin),
    .if(if),
    .b0(b0),
    .else(else),
    .b1(b1),
    .end(end)
);
