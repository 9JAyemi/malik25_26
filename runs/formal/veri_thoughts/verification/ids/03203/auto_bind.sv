// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_valid_fall_requires_handshake, assert, property, posedge, disable, iff, fell, past, check_overrun_single_cycle, check_frame_error_single_cycle, check_data_change_implies_valid, changed, check_data_change_while_busy, check_valid_rise_while_busy, rose
bind uart_rx uart_rx_assertions auto_sva_inst (
    .output_axis_tvalid(output_axis_tvalid),
    .output_axis_tready(output_axis_tready),
    .clk(clk),
    .rst(rst),
    .overrun_error(overrun_error),
    .frame_error(frame_error),
    .output_axis_tdata(output_axis_tdata),
    .busy(busy)
);
