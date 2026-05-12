property ResetSynceotid; @(posedge clk) (rst) |-> count == 0 ;endproperty 
 
 property SyncCounteotid; @(posedge clk) (rst) != 1'b1  |->  count == reg_18 ;endproperty 
 