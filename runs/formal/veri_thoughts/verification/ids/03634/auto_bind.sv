// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_adc_clk_mirrors_rx_clk, assert, property, posedge, disable, iff, check_adc_or_a_tied_low, b0, check_adc_or_b_tied_low, check_adc_data_a_s3_mapping, check_adc_data_a_s2_mapping, check_adc_data_a_s1_mapping, check_adc_data_a_s0_mapping, check_adc_data_b_s3_mapping, check_adc_data_b_s2_mapping, check_adc_data_b_s1_mapping, check_adc_data_b_s0_mapping, check_adc_status_clears_after_reset, check_adc_status_sets_after_nonreset, b1
bind axi_ad9234_if axi_ad9234_if_sva auto_sva_inst (
    .rx_clk(rx_clk),
    .rx_data(rx_data),
    .adc_clk(adc_clk),
    .adc_rst(adc_rst),
    .adc_data_a(adc_data_a),
    .adc_data_b(adc_data_b),
    .adc_or_a(adc_or_a),
    .adc_or_b(adc_or_b),
    .adc_status(adc_status)
);
