// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_xor_output, assert, property, posedge, check_mux_select_00, check_mux_select_01, check_mux_select_10, check_mux_select_11, b11, check_out_final_capture_xor, b0001, past, check_out_final_capture_inv_xor, b0010, check_out_final_force_zero, b0100, check_out_final_force_one, b1000, b1, check_out_final_hold_unmatched
bind xor_module top_module_sva auto_sva_inst (
    .clk(clk),
    .a(a),
    .b(b),
    .select(select),
    .mux_in(mux_in),
    .out_comb_ff(out_comb_ff),
    .mux_out(mux_out),
    .out_final(out_final),
    .b00(b00),
    .b0(b0),
    .b01(b01),
    .b10(b10)
);
