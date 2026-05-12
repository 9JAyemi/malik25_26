property ResetSynceotid; @(posedge clk) (reset) |-> state == 0 ;endproperty 
 
 property ValidCtrleotid; @(posedge clk) (reset) &&  (ena) |-> state == data ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (reset) &&  (!ena) |-> data == 0 ;endproperty 
 