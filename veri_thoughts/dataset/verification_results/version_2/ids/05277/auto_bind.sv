// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_write_reaches_q_after_two_cycles, assert, property, posedge, past, check_no_write_holds_q_after_two_cycles, check_back_to_back_writes_preserve_order, check_write_then_idle_holds_value, check_idle_then_write_delays_update
bind register_bank register_bank_sva auto_sva_inst (
    .clock(clock),
    .data(data),
    .rdaddress(rdaddress),
    .wraddress(wraddress),
    .wren(wren),
    .q(q)
);
