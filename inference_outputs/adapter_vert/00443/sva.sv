property ClockSynceotid; @(posedge clock_div_15) (X) |-> (or0_out) && (and0_out_X); endproperty 
 
 property ClockSynceotid; @(posedge clock_div_15) (or0_out) |-> (A2) || (A1); endproperty 
 
 property ClockSynceotid; @(posedge clock_div_15) (and0_out_X) |-> (or0_out) && (B1); endproperty 
 