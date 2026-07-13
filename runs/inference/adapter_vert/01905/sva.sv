property ResetSynceotid; @(posedge clk) (rst) |-> count == 0 ;endproperty 
 
 property EnableSynceotid; @(posedge clk) (en) && ! (rst)  |->  count == count + 1 ;endproperty 
 