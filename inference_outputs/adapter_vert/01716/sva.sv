property ResetSynceotid; @(posedge clk) (RST) |-> (COUNT) == 4'b0000 ;endproperty 
 
 property EnableSynceotid; @(posedge clk) (RST) != 1'b0 &&  (EN)  |-> (COUNT) == (COUNT) + 1'b1 ;endproperty 
 