// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_output, assert, property, posedge, h00, check_encrypt_on_enable, disable, iff, past, check_passthrough_when_disabled, check_zero_key_passthrough, check_zero_input_uses_key, check_self_xor_zero
bind mem_encrypt_decrypt mem_encrypt_decrypt_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .data_in(data_in),
    .key(key),
    .enable(enable),
    .data_out(data_out)
);
