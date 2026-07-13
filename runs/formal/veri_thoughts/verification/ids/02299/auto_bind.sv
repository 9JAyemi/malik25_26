// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_Q, assert, property, check_sel0_sa00_passthru, disable, iff, check_sel0_sa01_rotl1, check_sel0_sa10_sra1, check_sel0_sa11_rotl1, check_sel1_s00_passthru, check_sel1_s11_rotl1, check_sel1_s01_upper_from_A, check_sel1_s01_lsb_from_prev_shift3, past, check_sel1_s10_lower_from_A, check_sel1_s10_msb_from_prev_shift0
bind arithmetic_right_shift top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .A(A),
    .shift(shift),
    .shift_amount(shift_amount),
    .select(select),
    .Q(Q),
    .posedge(posedge),
    .b0000(b0000),
    .b00(b00),
    .b01(b01),
    .b10(b10),
    .b11(b11)
);
