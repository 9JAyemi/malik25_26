property ResetSynceotid; @(posedge clk) (rst) |-> (C) == 8'b00000000 ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) != 1'b1 |-> (C) == (A + B) ;endproperty 
 