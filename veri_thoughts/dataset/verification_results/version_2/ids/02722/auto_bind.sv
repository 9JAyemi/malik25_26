// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_write_capture_rd1, assert, property, posedge, past, check_write_capture_rd2, check_hold_no_write_rd1, check_hold_no_write_rd2, check_change_requires_prev_write_rd1, changed, check_change_requires_prev_write_rd2, check_prev_write_outputs_equal_written, check_any_change_implies_written_value, check_diff_implies_no_prev_write, check_equal_hold_without_write
bind register_bank register_bank_sva auto_sva_inst (
    .clk(clk),
    .data_in(data_in),
    .write_en(write_en),
    .read_address_1(read_address_1),
    .read_address_2(read_address_2),
    .read_data_1(read_data_1),
    .read_data_2(read_data_2)
);
