property ResetSynceotid; @(posedge clk) (reset) |-> (q == 0) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (reset) |-> (count == 0) ;endproperty 
 
 property SyncLoadeotid; @(posedge clk) (en) && !(reset) |-> (q == d) ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) && !(reset) |-> (count == 1) ;endproperty 
 