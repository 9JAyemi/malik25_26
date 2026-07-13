property SyncDataeotid; @(posedge clk_in_14) (ctrl) == (2'b00) |-> (data_out) == (bt_module_data_out); endproperty 
 
 property ValidDataeotid; @(posedge clk_in_14) (ctrl) == (2'b01) |-> (data_out) == (wifi_module_data_out); endproperty 
 
 property ValidDataeotid; @(posedge clk_in_14) (ctrl) == (2'b10) |-> (data_out) == (zigbee_module_data_out); endproperty 
 
 property ValidDataeotid; @(posedge clk_in_14) (ctrl) != 2'b00 && (ctrl) != 2'b01 && (ctrl) != 2'b10  |-> (data_out) == 8'b00000000; endproperty 
 