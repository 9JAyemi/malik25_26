property ResetSynceotid; @(posedge clk) (reset) |-> (X == 0) ;endproperty 
 
 property ValidSynceotid; @(posedge clk) (reset) != 1'b1  |-> (X == (A & B)) ;endproperty 
 