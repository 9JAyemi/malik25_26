property ResetSynceotid; @(posedge clk) (rst) |-> hold == 0 ;endproperty 
 
 property SyncLoadeotid; @(posedge clk) (rst) != 1'b1  |-> hold == in ;endproperty 
 
 property SyncDataeotid; @(posedge clk) (rst) != 1'b1  |-> out == hold ;endproperty 
 