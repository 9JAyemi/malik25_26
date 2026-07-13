property ResetSynceotid; @(posedge clk) (rst) |-> count == 4'b0 ;endproperty 
 
 property LoadSynceotid; @(posedge clk) (rst) &&  (load) |-> count == data ;endproperty 
 
 property SyncCounteotid; @(posedge clk) (rst) &&  (!load)  |-> count == count + 4'b1 ;endproperty 
 