// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): hold_when_no_trigger, assert, property, posedge, past, set0_on_trigger_no_ff_delayed, set1_on_trigger_ff_delayed_interleave0, toggle_on_trigger_ff_delayed_interleave1, toggle_dir_high_to_low, toggle_dir_low_to_high, change_only_on_trigger, changed, rise_implies_trigger_and_ff_delayed, rose, fall_implies_trigger, fell, next_state_on_trigger_matches_rtl
bind Interleaver Interleaver_sva auto_sva_inst (
    .clk(clk),
    .trigger(trigger),
    .Interleave_b(Interleave_b),
    .FF_en(FF_en),
    .output_en(output_en),
    .b0(b0),
    .b1(b1)
);
