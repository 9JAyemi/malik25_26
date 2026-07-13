property ResetSynceotid; @(posedge CLK) (RESET) |-> ENCLK == 0 ;endproperty 
 
 property EnableSynceotid; @(posedge CLK) (EN) && !(TE)  |-> ENCLK == ~CLK ;endproperty 
 
 property ClockSynceotid; @(posedge CLK) (EN) && (TE)  |-> ENCLK == 0 ;endproperty 
 
 property ClockSynceotid; @(posedge CLK) ! (EN)  |-> ENCLK == 0 ;endproperty 
 