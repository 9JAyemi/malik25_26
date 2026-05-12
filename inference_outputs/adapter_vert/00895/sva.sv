property ResetSynceotid; @(posedge clk) (rst) |-> count == 3'b0 ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) != 1'b0 |->  count == reg_14 ;endproperty 
 