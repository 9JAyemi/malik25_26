property ResetSynceotid; @(posedge clk) (rst) |-> count == 4'b0000 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (rst) != 1'b1 &&  (count) != 4'b1001  |->  (count) == (count + 1) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) != 1'b1 &&  (count) == 4'b1001  |->  (count) == 4'b0000 ;endproperty 
 