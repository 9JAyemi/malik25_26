property ResetSynceotid; @(posedge clk) (rst) |-> q == 0 ;endproperty 
 
 property LoadSynceotid; @(posedge clk) (rst) != 1'b1 &&  (ld) |-> q == d ;endproperty 
 