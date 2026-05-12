property ClockSynceotid; @(posedge clk_in_15) (A1) |-> (A2_A3) ;endproperty 
 
 property ClockSynceotid; @(posedge clk_in_15) (A2) &&  ( ! (A3) ) |-> (X) ;endproperty 
 