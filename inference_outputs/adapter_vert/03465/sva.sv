property ClockSynceotid; @(posedge clock_div_13) (A1) && (A2) && ! (B1) && ! (B2) |-> (X) ; endproperty 
 
 property SyncCheckeotid; @(posedge clock_div_13) ! (A1) && ! (A2) &&  (B1) &&  (B2) |-> (X) ; endproperty 
 
 property ClockSynceotid; @(posedge clock_div_13) (A1) && (A2) && ! (B1) && ! (B2) || ! (A1) && ! (A2) &&  (B1) &&  (B2) |->  (X)  ; endproperty 
 