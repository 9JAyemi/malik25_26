property ClockSynceotid; @(posedge clk_osc_15) (A1) && (A2) &&  (B1) && (B2) |-> (X) == 1'b1 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_15) (A1) && (A2) &&  !(B1) && !(B2)  &&  !(C1) &&  !(C2)  |-> (X) == 1'b1 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_15) !(A1) && !(A2)  &&  (B1) && (B2) |-> (X) == 1'b1 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_15) !(A1) && !(A2)  &&  !(B1) && !(B2)  &&  (C1) &&  (C2)  |-> (X) == 1'b0 ;endproperty 
 