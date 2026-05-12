property ClockSynceotid; @(posedge clk_in_11) (A1) && (A2) &&  ( !B1_N ) |-> (X) ;endproperty 
 property ValidSynceotid; @(posedge clk_in_11)  ( !A1 ) && (A2) &&  ( B1_N ) |-> (X) ;endproperty 
 