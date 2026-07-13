property ClockSynceotid; @(posedge clk_in_14) (a) |-> (temp_result) ;endproperty 
 
 property ValidReseteotid; @(posedge clk_in_14) (b) |-> (temp_result) ;endproperty 
 
 property ValidResulterreotid; @(posedge clk_in_14) (a) &&  (b) |-> (result) == (temp_result) ;endproperty 
 