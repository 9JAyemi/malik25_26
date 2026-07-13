property ClockSynceotid; @(posedge clk) (d) |-> (t) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (d) |-> (q) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (d) != (q) |-> (t) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (d) != (q) |-> (q) ;endproperty 
 