property ClockSynceotid; @(posedge clock_div_19) (Y) |-> (or0_out_Y == (not0_out && A_N)); endproperty 
 
 property ClockSynceotid; @(posedge clock_div_19) (or0_out_Y) |-> (Y == (or0_out_Y)); endproperty 
 
 property ClockSynceotid; @(posedge clock_div_19) (not0_out) == (1'b1) &&  (B) |->  (or0_out_Y) ; endproperty 
 