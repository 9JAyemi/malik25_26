// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, check_lower_add_split, assert, property, posedge, disable, iff, b0, check_upper_add_split, check_full_65bit_sum, check_cout32_is_lower_carry, check_lo_bits_match, check_cout64_is_upper_carry, check_hi_bits_match, check_cout64_matches_total_carry, check_adder_out_matches_total_low64, check_lo_outputs_stable_on_lo_inputs_stable, stable, check_hi_outputs_stable_on_hi_inputs_and_cout32_stable
bind sparc_exu_aluadder64 sparc_exu_aluadder64_sva auto_sva_inst (
    .rs1_data(rs1_data),
    .rs2_data(rs2_data),
    .cin(cin),
    .adder_out(adder_out),
    .cout32(cout32),
    .cout64(cout64)
);
