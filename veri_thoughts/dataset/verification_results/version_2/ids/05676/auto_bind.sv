// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_signal_valid_definition, assert, property, posedge, disable, iff, check_valid_requires_minute_parity, check_valid_requires_hour_parity, check_valid_requires_date_parity, check_valid_requires_bit0_zero, check_valid_requires_bit20_one, check_valid_requires_new_second, check_all_conditions_imply_valid
bind dcf77_validy_checker dcf77_validy_checker_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .dcf_bits(dcf_bits),
    .dcf_new_sec(dcf_new_sec),
    .signal_valid(signal_valid),
    .parity_min(parity_min),
    .parity_hour(parity_hour),
    .parity_date(parity_date),
    .assign(assign),
    .b0(b0),
    .b1(b1)
);
