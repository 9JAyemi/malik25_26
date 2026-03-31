module wireless_communication_block_sva (
    input logic clk,
    input logic [7:0] data_in,
    input logic [1:0] ctrl,
    input logic [7:0] data_out
);

    // When ctrl == 2'b00 (Bluetooth), data_out must equal data_in.
    check_bt_select_passthrough: assert property (
        @(posedge clk) (ctrl == 2'b00) |-> (data_out == data_in)
    );

    // When ctrl == 2'b01 (WiFi), data_out must equal data_in.
    check_wifi_select_passthrough: assert property (
        @(posedge clk) (ctrl == 2'b01) |-> (data_out == data_in)
    );

    // When ctrl == 2'b10 (ZigBee), data_out must equal data_in.
    check_zigbee_select_passthrough: assert property (
        @(posedge clk) (ctrl == 2'b10) |-> (data_out == data_in)
    );

    // When ctrl == 2'b11 (default), data_out must be zero.
    check_default_zero_output: assert property (
        @(posedge clk) (ctrl == 2'b11) |-> (data_out == 8'h00)
    );

    // For any non-default selection (00/01/10), data_out must equal data_in.
    check_nondefault_passthrough: assert property (
        @(posedge clk) (ctrl != 2'b11) |-> (data_out == data_in)
    );

    // If non-default selection holds across cycles and data_in is stable, data_out is stable.
    check_stable_when_nondefault_and_input_stable: assert property (
        @(posedge clk) ($past(ctrl != 2'b11) && (ctrl != 2'b11) && $stable(data_in)) |-> $stable(data_out)
    );

    // If non-default selection holds across cycles and data_in changes, data_out changes.
    check_change_propagates_when_nondefault_held: assert property (
        @(posedge clk) ($past(ctrl != 2'b11) && (ctrl != 2'b11) && $changed(data_in)) |-> $changed(data_out)
    );

    // If default selection holds across cycles, data_out stays zero and stable.
    check_zero_stability_when_default_held: assert property (
        @(posedge clk) ($past(ctrl == 2'b11) && (ctrl == 2'b11)) |-> ($stable(data_out) && (data_out == 8'h00))
    );

endmodule