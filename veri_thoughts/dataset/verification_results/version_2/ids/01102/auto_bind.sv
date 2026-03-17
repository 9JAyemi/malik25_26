// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_master_ack_select, assert, property, posedge, check_master_data_mux_select, check_slave_addr_map, b0, check_slave_dat_o_passthrough, check_slave_we_passthrough, check_slave_stb_exact_pattern, h1, h0, check_slave_stb_selected_bit, check_slave_stb_unselected_zero, check_slave_stb_onehot_when_asserted, onehot
bind WB_intercon WB_intercon_sva auto_sva_inst (
    .master_STB(master_STB),
    .master_WE(master_WE),
    .master_DAT_I(master_DAT_I),
    .master_ADDR(master_ADDR),
    .slave_DAT_I(slave_DAT_I),
    .slave_ACK(slave_ACK),
    .master_DAT_O(master_DAT_O),
    .slave_DAT_O(slave_DAT_O),
    .slave_ADDR(slave_ADDR),
    .slave_STB(slave_STB),
    .master_ACK(master_ACK),
    .slave_WE(slave_WE)
);
