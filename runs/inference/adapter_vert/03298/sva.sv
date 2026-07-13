property ClockSynceotid; @(posedge clk_in_19) (A1) == (1) &&  (A2) == (0) &&  (B1) == (1) &&  (C1) == (0) &&  (D1) == (1) |-> (X) == 1 ;endproperty 
 property SyncCheckeotid; @(posedge clk_in_19) (A1) == (1) &&  (A2) == (0) &&  (B1) != 1 &&  (C1) != 0 &&  (D1) != 1 |-> (X) == 0 ;endproperty 
 property SyncCheckeotid; @(posedge clk_in_19) (A1) != 1 ||  (A2) != 0 ||  (B1) != 1 ||  (C1) != 0 ||  (D1) != 1 |-> (X) == 0 ;endproperty 
 