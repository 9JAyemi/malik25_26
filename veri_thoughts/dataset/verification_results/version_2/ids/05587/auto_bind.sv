// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): Lfsr, check_reset_clears_state, assert, property, posedge, h0000, b0, check_enable_sets_done, disable, iff, b1, check_disable_clears_done, check_disable_holds_data, stable, check_disable_holds_lfsr, check_enable_captures_lfsr_into_data, past, check_enable_updates_lfsr
bind lfsr lfsr_sva auto_sva_inst (
    .Clk(Clk),
    .Reset(Reset),
    .Seed(Seed),
    .Enable(Enable),
    .Data(Data),
    .Done(Done)
);
