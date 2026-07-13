property ClockSynceotid; @(posedge clk_in_1) (A0) |-> (SA) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (A1) |-> (SB) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (A2) |-> (SC) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (A3) |-> (SD) ; endproperty 
 
 property ValidSynceotid; @(posedge clk_in_1) (SA) ||  (SB)  |-> (SE) ; endproperty 
 
 property ValidSynceotid; @(posedge clk_in_1) (SC) ||  (SD)  |-> (SF) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (SE) &&  ( !S1 )  |-> (SG) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (SF) &&  ( S1 )  |-> (SH) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1)  (SG)  ||  (SH)  ==  (X) ; endproperty 
 