property ResetSynceotid; @(posedge clk) (reset) |-> q == 4'b0000 ;endproperty 
 
 property EnableSynceotid; @(posedge clk) (enable) && !(reset) |-> q == reg_1 ;endproperty 
 