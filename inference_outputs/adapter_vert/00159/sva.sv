property ResetSynceotid; @(posedge clk) (reset) |-> (q) == 4'b0000 ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (reset) &&  (q) == 4'b1111  |-> (q) == 4'b0000; endproperty 
 
 property SyncInceotid; @(posedge clk) (reset) != 1'b1  &&  (q) != 4'b1111  |-> (q) == (q + 1'b1); endproperty 
 