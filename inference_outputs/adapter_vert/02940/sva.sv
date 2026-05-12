property ResetSynceotid; @(posedge clk) (reset) |-> result == 4'b0000 ;endproperty 
 
 property AddOnReseteotid; @(posedge clk) (reset) &&  (  operation == 0 ) |-> result == (A + B) ;endproperty 
 
 property SubOnReseteotid; @(posedge clk) (reset) &&  (  operation != 0 ) |-> result == (A - B) ;endproperty 
 