module wireless_communication_block_sva (
    input logic bt_module_data_out,
    input logic ctrl,
    input logic data_out,
    input logic wifi_module_data_out,
    input logic zigbee_module_data_out,
    input logic b00,
    input logic b00000000,
    input logic b01,
    input logic b10,
    input logic clk_in_14
);

property SyncDataeotid; @(posedge clk_in_14) (ctrl) == (2'b00) |-> (data_out) == (bt_module_data_out); endproperty
assert property (SyncDataeotid);

property ValidDataeotid; @(posedge clk_in_14) (ctrl) == (2'b01) |-> (data_out) == (wifi_module_data_out); endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_14) (ctrl) == (2'b10) |-> (data_out) == (zigbee_module_data_out); endproperty
assert property (ValidDataeotid_2);

property ValidDataeotid_3; @(posedge clk_in_14) (ctrl) != 2'b00 && (ctrl) != 2'b01 && (ctrl) != 2'b10  |-> (data_out) == 8'b00000000; endproperty
assert property (ValidDataeotid_3);

endmodule