property ClockSynceotid; @(posedge clk_in_12) (B) |-> (E) ;endproperty 
 
 property ValidIneotid; @(posedge clk_in_12) (in) |-> (out) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_12) (B) |-> (D) ;endproperty 
 