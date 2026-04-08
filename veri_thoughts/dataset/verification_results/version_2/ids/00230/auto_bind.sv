// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): g_disabled, check_disabled_valid_passthrough, assert, property, posedge, g_disabled_narrow, check_disabled_data_zero_extend, b0, check_disabled_upper_zero, g_disabled_wide, check_disabled_data_word_copy, g_enabled, check_enabled_valid_pipeline, b1, past, g_enabled_low_bits, check_enabled_lower_bits_pipeline, check_enabled_sign_bit_format, check_enabled_type_zero_preserve_sign, check_enabled_type_one_invert_sign, g_enabled_narrow, check_enabled_upper_zero_without_signext, check_enabled_upper_signext, check_enabled_dfmt_disable_zero_extend, g_enabled_wide, check_enabled_dfmt_disable_word_copy
bind ad_datafmt ad_datafmt_sva auto_sva_inst (
    .clk(clk),
    .valid(valid),
    .DATA_WIDTH(DATA_WIDTH),
    .data(data),
    .valid_out(valid_out),
    .data_out(data_out),
    .dfmt_enable(dfmt_enable),
    .dfmt_type(dfmt_type),
    .dfmt_se(dfmt_se),
    .generate(generate),
    .if(if),
    .DISABLE(DISABLE),
    .begin(begin),
    .end(end),
    .else(else)
);
