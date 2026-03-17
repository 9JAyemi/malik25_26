// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): dff_loads_d_on_negedge, assert, property, disable, iff, past, dff_prev_reset_drives_zero, h00, dff_reset_now_zero_next, or_exact_decomposition, or_includes_q_xor_d, or_includes_prev_q_toggle, or_reduces_to_prev_anyedge_when_qeqd, or_zero_when_no_sources, or_after_reset_reduces_to_q_xor_d
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .d(d),
    .q(q),
    .anyedge_or_d(anyedge_or_d),
    .negedge(negedge),
    .posedge(posedge)
);
