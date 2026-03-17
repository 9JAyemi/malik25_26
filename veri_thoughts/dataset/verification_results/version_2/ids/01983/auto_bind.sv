// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_forces_out_zero, assert, property, d0, out_matches_prev_product_when_no_reset, disable, iff, past, out_zero_if_prev_cycle_in_reset, out_lo_matches_out_lsb_when_active, out_lo_matches_prev_product_lsb, out_lo_zero_if_prev_cycle_in_reset, out_eq_in2_when_mul_by_one_on_in1, d1, out_eq_in1_when_mul_by_one_on_in2, out_zero_when_either_operand_prev_zero, out_equals_255x255_when_prev_inputs_ff, hFF, hFE01
bind mult_module mult_system_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .in1(in1),
    .in2(in2),
    .out(out),
    .out_lo(out_lo),
    .posedge(posedge)
);
