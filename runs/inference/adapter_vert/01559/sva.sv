property ResetSynceotid; @(posedge clk) (rst) |-> count == 0 ;endproperty 
 
 property EnableSynceotid; @(posedge clk) (enable) && !(rst) |-> count == count + 1 ;endproperty 
 