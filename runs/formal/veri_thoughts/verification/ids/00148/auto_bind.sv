// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): RP_ID, hA0, check_status_constant, assert, property, posedge, h0, check_enable_pipeline, b1, past, check_valid_pipeline, check_data_pipeline
bind adc_fifo adc_fifo_sva auto_sva_inst (
    .clk(clk),
    .control(control),
    .status(status),
    .src_adc_enable(src_adc_enable),
    .src_adc_valid(src_adc_valid),
    .src_adc_data(src_adc_data),
    .dst_adc_enable(dst_adc_enable),
    .dst_adc_valid(dst_adc_valid),
    .dst_adc_data(dst_adc_data)
);
