module wireless_communication_block_sva (
    input logic [7:0] data_in,
    input logic [1:0] ctrl,
    input logic [7:0] data_out
);

    // ctrl=00 selects the Bluetooth path.
    check_ctrl_00_selects_bt: assert property (
        @($global_clock) (ctrl == 2'b00) |-> (data_out == data_in)
    );

    // ctrl=01 selects the Wi-Fi path.
    check_ctrl_01_selects_wifi: assert property (
        @($global_clock) (ctrl == 2'b01) |-> (data_out == data_in)
    );

    // ctrl=10 selects the Zigbee path.
    check_ctrl_10_selects_zigbee: assert property (
        @($global_clock) (ctrl == 2'b10) |-> (data_out == data_in)
    );

    // ctrl=11 drives zero on the output.
    check_ctrl_11_drives_zero: assert property (
        @($global_clock) (ctrl == 2'b11) |-> (data_out == 8'h00)
    );

    // Any non-zero output must come from the selected path.
    check_nonzero_output_has_valid_source: assert property (
        @($global_clock) (data_out != 8'h00) |-> ((ctrl == 2'b00) || (ctrl == 2'b01) || (ctrl == 2'b10))
    );

endmodule