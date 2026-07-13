property ClockSynceotid; @(posedge clk_in_14) (Y) |-> (not0_out_Y) ;endproperty 
 
 property ClockSynceotid; @(posedge clk_in_14) (A) |-> (not0_out_Y) ;endproperty 
 
 property ClockSynceotid; @(posedge clk_in_14) (not0_out_Y) == (1'b1) &&  ( (A) ) |-> (Y) == (1'b1) ;endproperty 
 
 property ClockSynceotid; @(posedge clk_in_14) (not0_out_Y) != 1'b1  &&  ( (A) ) |-> (Y) != 1'b1 ;endproperty 
 