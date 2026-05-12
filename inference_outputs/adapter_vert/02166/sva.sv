property ResetSynceotid; @(posedge clk) (rst) |-> sum == 8'b0 ;endproperty 
 
 property SyncAccumulateeotid; @(posedge clk) (rst) != 1'b1  |-> sum == data_in + sum; endproperty 
 
 property SyncAccumulateeotid; @(posedge clk) (rst) != 1'b1  |-> out == sum; endproperty 
 