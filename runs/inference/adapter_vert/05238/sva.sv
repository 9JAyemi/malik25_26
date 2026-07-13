property ClockSynceotid; @(posedge clk_in_15) (A) |-> (or_output) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_15) (B) |-> (or_output) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_15) (C) != 1'b1 ||  (or_output)  == 1'b0 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_15) (C) == 1'b1 &&  (or_output)  != 1'b0 ;endproperty 
 