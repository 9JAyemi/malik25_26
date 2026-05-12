property ResetSynceotid; @(posedge clk) (rst) |-> count == 4'b0 ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) != 1'b1 |->  count == reg_14 ;endproperty 
 