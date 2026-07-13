property ClockSynceotid; @(posedge clk_in_15) (EN) |-> (ECK) ;endproperty 
 
 property ClockSynceotid; @(posedge clk_in_15) (EN) &&  ( ! (SE) ) |-> (O) == (I) ;endproperty 
 