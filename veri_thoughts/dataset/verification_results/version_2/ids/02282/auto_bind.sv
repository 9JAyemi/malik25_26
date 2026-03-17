// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): stage1, stage2, stage3, stage4, check_data_out_mirrors_stage4, assert, property, posedge, check_load_stage1_from_data_in, past, check_load_stage2_from_stage1, check_load_stage3_from_stage2, check_load_stage4_from_stage3, check_shr_stage1_from_stage4, check_shr_stage2_from_stage1, check_shr_stage3_from_stage2, check_shr_stage4_from_stage3, check_shl_stage1_from_stage2, check_shl_stage2_from_stage3, check_shl_stage3_from_stage4, check_shl_stage4_from_data_in
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .data_in(data_in),
    .shift_right(shift_right),
    .load(load),
    .data_out(data_out)
);
