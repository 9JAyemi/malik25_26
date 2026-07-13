property ClockSynceotid; @(posedge clk) (d) |-> (q1) ;endproperty 
 
 property SyncCheckeotid; @(negedge clk) (q1) |-> (q2) ;endproperty 
 
 property SyncCheckeotid; @(negedge clk) (q2) == (q) ;endproperty 
 