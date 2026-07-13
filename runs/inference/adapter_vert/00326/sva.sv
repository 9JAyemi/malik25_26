property ResetSynceotid; @(posedge clk) (reset) |-> count == 0 ;endproperty 
 
 property SyncCounteotid; @(posedge clk) (reset) != 1'b1  |->  count == count + 1 ;endproperty 
 