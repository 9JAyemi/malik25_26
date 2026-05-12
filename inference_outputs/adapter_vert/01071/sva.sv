property ClockSynceotid; @(posedge clock_div_19) (X) |-> (and0_out) && (or0_out_X); endproperty 
 
 property ValidSynceotid; @(posedge clock_div_19) (and0_out) &&  (  (A1) && (A2)  ) ; endproperty 
 
 property ValidSynceotid; @(posedge clock_div_19) (or0_out_X) |->  (  (and0_out) && (C1) || (B1)  ) ; endproperty 
 
 property ClockSynceotid; @(posedge clock_div_19) (X) == (or0_out_X) ; endproperty 
 