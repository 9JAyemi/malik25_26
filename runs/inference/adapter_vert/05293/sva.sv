property ResetSynceotid; @(posedge clk) (rst) |-> count == 0 ;endproperty 
 
 property LoadSynceotid; @(posedge clk) (load) |-> count == data ;endproperty 
 
 property SyncCounteotid; @(posedge clk) ( !rst && !load ) |-> count == count + 1 ;endproperty 
 