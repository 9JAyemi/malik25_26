property ResetSynceotid; @(posedge clk) (reset) |-> stored_data == 0 && out_valid == 0 ;endproperty 
 
 property ValidDataeotid; @(posedge clk) (reset) != 1'b1 &&  (in_valid) |-> stored_data == in_data && out_valid == 1 ;endproperty 
 
 property ValidDataeotid; @(posedge clk) (reset) != 1'b1 &&  !(in_valid)  |-> out_valid == 0 ;endproperty 
 
 property SyncDataeotid; @(posedge clk) (reset) != 1'b1  |-> out_data == stored_data; endproperty 
 