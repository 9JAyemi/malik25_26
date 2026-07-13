property ResetSynceotid; @(posedge clk) (reset) |-> (count == 4'b0); endproperty 
 
 property ResetSynceotid; @(posedge clk) (reset) &&  (enable) |-> (count == reg_13); endproperty 
 