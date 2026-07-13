// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): counter, freq, secondcounter, stopin, inreseted, SECONDCOUNT, d8001800, check_frequency_tied_to_internal, assert, property, posedge, check_secondcounter_resets_on_hit, d0, check_freq_updates_on_hit, past, check_stopin_set_on_hit_no_inreseted, b1, check_stopin_clears_when_inreseted, b0, check_stopin_only_deasserts_when_inreseted, fell, check_stopin_only_asserts_on_hit_without_inreseted, rose, check_secondcounter_increments_when_active, d1, check_secondcounter_holds_when_stopped, check_freq_changes_only_on_hit, changed, check_counter_stable_without_fall, check_counter_increments_on_fall_while_counting, check_counter_reset_and_inreseted_set_on_fall_while_stopped, check_inreseted_cleared_on_fall_while_counting
bind FrequencyCounter FrequencyCounter_sva auto_sva_inst (
    .clk(clk),
    .freqin(freqin),
    .frequency(frequency)
);
