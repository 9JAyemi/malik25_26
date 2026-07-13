property ResetSynceotid; @(posedge clk) (reset) |-> (count == 4'b0) && (out == 1'b0) ;endproperty 
 
 property SyncIncrseotid; @(posedge clk) (reset) != 1'b1  |->  (count == reg_15) && (out != reg_16) ;endproperty 
 