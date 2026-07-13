// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, check_seq_out_on_input_change, disable, iff, initstate, past, check_seq_out_stable_on_input_stable, check_change_out_masked_vector, check_final_out_is_or_of_parts, check_final_out_matches_out, check_change_out_reflects_masked_change, check_change_out_stable_on_masked_stable
bind sequence_edge_detection top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .in(in),
    .out(out),
    .seq_out(seq_out),
    .change_out(change_out),
    .final_out(final_out),
    .posedge(posedge),
    .b0(b0)
);
