// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): cross_int, active0, active1, active0_next, active1_next, reset_active0_low, assert, property, posedge, b0, reset_active1_low, reset_cross_int_low, mux_passthrough_when_no_cross, disable, iff, mux_swap_when_cross, b1, active0_updates_on_handshake, past, active0_holds_without_handshake, active1_updates_on_handshake, active1_holds_without_handshake, cross_int_changes_only_when_idle, changed, cross_int_holds_when_busy, cross_int_updates_from_cross_when_idle
bind crossbar36 crossbar36_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .clear(clear),
    .cross(cross),
    .data0_i(data0_i),
    .src0_rdy_i(src0_rdy_i),
    .dst0_rdy_o(dst0_rdy_o),
    .data1_i(data1_i),
    .src1_rdy_i(src1_rdy_i),
    .dst1_rdy_o(dst1_rdy_o),
    .data0_o(data0_o),
    .src0_rdy_o(src0_rdy_o),
    .dst0_rdy_i(dst0_rdy_i),
    .data1_o(data1_o),
    .src1_rdy_o(src1_rdy_o),
    .dst1_rdy_i(dst1_rdy_i)
);
