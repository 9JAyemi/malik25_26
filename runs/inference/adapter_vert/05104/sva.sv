property ResetSynceotid; @(posedge clk) (reset) |-> count == 2'b0 ;endproperty 
 
 property EnableSynceotid; @(posedge clk) (enable) && !(reset) |->  count == reg_16 ;endproperty 
 
 