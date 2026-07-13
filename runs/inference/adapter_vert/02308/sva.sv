property SyncNandCheckeotid; @(posedge clk) (in1) && (in2) |-> !out ;endproperty 
 
 property SyncNandCheckeotid; @(posedge clk) (in1) && !(in2) |->  out ;endproperty 
 
 property SyncNandCheckeotid; @(posedge clk) !(in1) && (in2) |->  out ;endproperty 
 
 property SyncNandCheckeotid; @(posedge clk) !(in1) && !(in2) |->  out ;endproperty 
 