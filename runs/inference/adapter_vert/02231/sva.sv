property ResetSynceotid; @(posedge clk) (xclear) |-> xout == 0 ;endproperty 
 
 property LoadSynceotid; @(posedge clk) (xload) |-> xout == xin ;endproperty 
 