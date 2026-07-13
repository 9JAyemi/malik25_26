// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): encrypted_data, reset_clears_regs, assert, property, posedge, h00, en0_holds_encrypted, disable, iff, past, en1_updates_encrypted, en0_bypass_data_out, en1_pipeline_data_out, data_out_prev_mux, encrypted_prev_mux, back_to_back_enable_pipeline
bind mem_encrypt_decrypt mem_encrypt_decrypt_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .data_in(data_in),
    .key(key),
    .enable(enable),
    .data_out(data_out)
);
