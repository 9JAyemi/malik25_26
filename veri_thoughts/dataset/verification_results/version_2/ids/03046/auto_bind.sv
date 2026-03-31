// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, check_tx_ready_asserts_on_valid_and_ready, disable, iff, check_tx_ready_deasserts_without_valid_or_ready, check_rx_data_holds_value, b1, stable, EtherCAT_slave_sva, check_reset_clears_tx_outputs, check_reset_clears_rx_outputs, check_tx_data_holds_value, check_valid_outputs_assert_on_ready, check_valid_outputs_deassert_without_ready, check_rx_ready_asserts_outside_reset
bind EtherCAT_master EtherCAT_master_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .tx_data(tx_data),
    .tx_valid(tx_valid),
    .rx_data(rx_data),
    .rx_valid(rx_valid),
    .tx_ready(tx_ready),
    .rx_ready(rx_ready),
    .posedge(posedge),
    .b0(b0),
    .endmodule(endmodule),
    .module(module)
);
