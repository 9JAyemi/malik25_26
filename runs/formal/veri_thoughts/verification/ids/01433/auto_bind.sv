// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_eop_implies_idle_and_prev_not_idle, assert, property, past, check_idle_rise_implies_eop, check_eop_one_cycle_pulse, check_data_ready_one_cycle_pulse, check_idle_excludes_data_ready, check_data_ready_excludes_idle, check_data_ready_excludes_eop, check_idle_steady_no_eop, check_idle_fall_excludes_eop_and_data_ready, check_data_stable_on_ready, check_data_stable_while_idle
bind SerialRX SerialRX_sva auto_sva_inst (
    .clk(clk),
    .RxD(RxD),
    .RxD_data_ready(RxD_data_ready),
    .RxD_data(RxD_data),
    .RxD_endofpacket(RxD_endofpacket),
    .RxD_idle(RxD_idle),
    .posedge(posedge),
    .b0(b0)
);
