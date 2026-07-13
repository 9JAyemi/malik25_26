// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_data_out, assert, property, posedge, h00, pass_through_when_disabled, disable, iff, past, encrypt_when_enabled, pass_through_when_key_zero, zero_when_data_equals_key, key_when_data_zero, invert_when_key_all_ones, hFF, invert_key_when_data_all_ones, invert_when_key_zero, key_when_data_equals_not_key
bind mem_encrypt_decrypt mem_encrypt_decrypt_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .data_in(data_in),
    .key(key),
    .enable(enable),
    .data_out(data_out)
);
