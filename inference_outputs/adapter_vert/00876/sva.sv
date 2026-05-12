property ClockSynceotid; @(posedge clk_in_15) (A1) && (A2) |-> (Y) == 1'b1 ;endproperty 
 
 property ClockSynceotid; @(posedge clk_in_15) (A1) && !(A2) && (B1) |-> (Y) == 1'b1 ;endproperty 
 
 property ClockSynceotid; @(posedge clk_in_15) !(A1) && (A2) && (B1) |-> (Y) == 1'b1 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_15) !(A1) && !(A2) && !(B1) |-> (Y) == 1'b0 ;endproperty 
 