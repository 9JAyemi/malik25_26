property ResetSynceotid; @(posedge clk) (rst) |-> count == 2'b00 ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) &&  (en) &&  (count != 2'b11)  |-> count == count + 1 ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) &&  (en) &&  (count == 2'b11)  |-> count == 2'b00 ;endproperty 
 