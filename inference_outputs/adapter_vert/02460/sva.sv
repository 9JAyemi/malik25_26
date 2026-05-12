property ClockSynceotid; @(posedge clock_div_15) (X) |-> (or0_out) ;endproperty 
 
 property ClockSynceotid; @(posedge clock_div_15) (X) |-> (and0_out_X) ;endproperty 
 
 property ClockSynceotid; @(posedge clock_div_15) (X) == (and0_out_X) ;endproperty 
 