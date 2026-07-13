property ResetSynceotid; @(posedge clk) (reset) |-> count == 4'b0000 ;endproperty 
 
 property SyncCounteotid; @(posedge clk) (reset) != 1'b1 &&  (count) != 4'b1111  |->  (count) == (count + 4'b0001) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (reset) != 1'b1 &&  (count) == 4'b1111  |->  (count) == 4'b0000 ;endproperty 
 