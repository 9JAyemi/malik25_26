property ClockSynceotid; @(posedge clock_div_19) (Y) |-> (not0_out_Y) ;endproperty 
 
 property ClockSynceotid; @(posedge clock_div_19) (not0_out_Y) == (1'b1) &&  (  A  != 1'b1  ) |->  (Y) != 1'b1 ;endproperty 
 
 property ClockSynceotid; @(posedge clock_div_19) (not0_out_Y) != 1'b1  &&  (  A  != 1'b1  ) |->  (Y) != 1'b1 ;endproperty 
 
 property ClockSynceotid; @(posedge clock_div_19) (not0_out_Y) != 1'b1  &&  (  A  == 1'b1  ) |->  (Y) == 1'b0 ;endproperty 
 