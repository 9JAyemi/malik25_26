property DataSynceotid; @(posedge clk_in_1) (data) |-> (parity_error) == (xor_result == 1); endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (data) |-> (xor_result) == (data); endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (data) |-> (parity_error) != 7'b0xxxxxx; endproperty 
 