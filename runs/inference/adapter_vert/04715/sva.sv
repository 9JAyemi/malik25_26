property ResetSynceotid; @(posedge clk) (reset) |-> count == 4'b0000 ;endproperty 
 
 property EnableSynceotid; @(posedge clk) (reset) != 1'b1 &&  (enable) |-> count == reg_15 ;endproperty 
 
 property SyncCtrleotid; @(posedge clk) (reset) != 1'b1 &&  !(enable)  |-> count == reg_16 ;endproperty 
 