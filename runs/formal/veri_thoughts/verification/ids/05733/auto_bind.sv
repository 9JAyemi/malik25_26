// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_goto_matches_state1a, assert, property, posedge, check_state_decodes_mutex, check_out1_definition, check_idle_to_state1_on_ram_valid, check_idle_holds_without_ram_valid, check_state1_to_state0_when_start_low, check_state1_holds_when_start_high, check_out1_only_in_state0, check_out1_leads_to_state1
bind axi_ethernet_ram_reader axi_ethernet_ram_reader_sva auto_sva_inst (
    .state1a(state1a),
    .goto_readDestAdrNib1(goto_readDestAdrNib1),
    .state0a(state0a),
    .out_1(out_1),
    .ram_valid_i(ram_valid_i),
    .s_axi_aclk(s_axi_aclk),
    .AR(AR),
    .startReadDestAdrNib(startReadDestAdrNib),
    .Q(Q)
);
