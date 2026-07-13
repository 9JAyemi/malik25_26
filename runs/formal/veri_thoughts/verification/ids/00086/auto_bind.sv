// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, or_result, function, automatic, expected_shift, d_i, shift_i, endfunction, expected_alu, a_i, b_i, ctrl_i, check_shifted_d_matches_spec, assert, property, posedge, check_shift_default_passthrough, check_alu_result_matches_spec, check_alu_default_passthrough, check_or_result_composition, b0, check_result_tracks_or_result, check_result_upper_half_matches_alu, check_result_contains_shift_ones, check_result_contains_alu_ones, check_result_matches_full_spec
bind barrel_shifter_16bit top_module_sva auto_sva_inst (
    .D(D),
    .shift_ctrl(shift_ctrl),
    .a(a),
    .b(b),
    .alu_ctrl(alu_ctrl),
    .result(result),
    .shifted_D(shifted_D),
    .alu_result(alu_result),
    .case(case),
    .b0000(b0000),
    .b0001(b0001),
    .b0010(b0010),
    .b0011(b0011),
    .b0100(b0100),
    .b0101(b0101),
    .b0110(b0110),
    .b0111(b0111),
    .default(default),
    .endcase(endcase)
);
