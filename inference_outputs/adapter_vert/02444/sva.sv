property ClockSynceotid; @(posedge clk_in_14) (A) |-> (Z) ;endproperty 
 
 property ClockSynceotid; @(posedge clk_in_14) (TE_B) != (A) && (TE_B) |-> (Z) == 1'b0 ;endproperty 
 