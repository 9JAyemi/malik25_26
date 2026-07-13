property ClockSynceotid; @(posedge clock_div_19) (Y) |-> (nand0_out) && (nand1_out) && (and0_out_Y); endproperty 
 
 property ClockSynceotid; @(posedge clock_div_19) (Y) == (1'b1) |-> (nand0_out) && (nand1_out) && (and0_out_Y); endproperty 
 
 property ClockSynceotid; @(posedge clock_div_19) (Y) != 1'b1  |->  !( (nand0_out) && (nand1_out) && (and0_out_Y) ) ; endproperty 
 