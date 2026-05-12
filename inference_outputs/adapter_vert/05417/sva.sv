property ResetSynceotid; @(posedge clk) (reset) |-> count == 4'b0 ;endproperty 
 
 property LoadSynceotid; @(posedge clk) (load) && !(reset)  |-> count == data_in ;endproperty 
 
 property SyncCounteotid; @(posedge clk) !(reset) && ! (load)  |-> count == count + 1 ;endproperty 
 