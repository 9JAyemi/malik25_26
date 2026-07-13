property ClockSynceotid; @(posedge clock_div_14) (and0_out) |-> (A3 == 1'b1) && (A1 == 1'b1) && (A2 == 1'b1); endproperty 
 
 property ClockSynceotid; @(posedge clock_div_14) (nor0_out_Y) |-> (and0_out != 1'b1) || (B1 != 1'b1) || (C1 != 1'b1); endproperty 
 
 property ClockSynceotid; @(posedge clock_div_14) (Y) == (nor0_out_Y); endproperty 
 