// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_parity_definition, assert, property, posedge, check_stable_when_data_stable, stable, check_error_change_implies_data_change, changed, check_data_change_implies_error_change, check_zero_data_implies_no_error, h00, b0, check_all_ones_implies_no_error, hFF, check_even_parity_implies_no_error, check_odd_parity_implies_error, b1, check_single_bit_toggle_toggles_error, onehot, check_two_bit_toggle_keeps_error
bind parity_check parity_check_sva auto_sva_inst (
    .data(data),
    .parity_error(parity_error)
);
