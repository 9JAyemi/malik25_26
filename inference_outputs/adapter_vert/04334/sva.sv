property ResetSynceotid; @(posedge CLK) (RST) |-> DATA_OUT == 0 ;endproperty 
 
 property ResetSynceotid; @(posedge CLK) (RST) != 1'b1 &&  (DATA_OUT) == 8'hf4  |->  (DATA_OUT) == 8'hc2 ;endproperty 
 
 property ResetSynceotid; @(posedge CLK) (RST) != 1'b1 &&  (DATA_OUT) != 8'hf4  |->  (DATA_OUT) == 8'hf4 ;endproperty 
 