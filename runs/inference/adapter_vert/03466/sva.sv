property SyncIneotid; @(posedge clk) (in) |-> (shiftreg) == (4'b0110) ;endproperty 
 
 property SyncRiseeotid; @(posedge clk) (in) |-> (rising) ;endproperty 
 
 property SyncFalleotid; @(posedge clk) (in) |-> (falling) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (in) |-> (out) == (shiftreg) ;endproperty 
 