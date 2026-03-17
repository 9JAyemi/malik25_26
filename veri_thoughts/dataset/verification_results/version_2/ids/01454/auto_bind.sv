// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_wb_ack_definition, assert, property, disable, iff, check_wb_ack_stability_if_inputs_stable, stable, check_write_implies_ack, b1, check_speaker_definition, check_speaker_stability_if_inputs_stable, check_reset_clears_data_next, h00, check_write_updates_data_next, past, check_hold_without_write, check_data_changes_only_on_write_or_reset, changed, check_data_zero_when_reset_held
bind speaker speaker_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .wb_dat_i(wb_dat_i),
    .wb_dat_o(wb_dat_o),
    .wb_we_i(wb_we_i),
    .wb_stb_i(wb_stb_i),
    .wb_cyc_i(wb_cyc_i),
    .wb_ack_o(wb_ack_o),
    .timer2(timer2),
    .speaker_(speaker_),
    .posedge(posedge)
);
