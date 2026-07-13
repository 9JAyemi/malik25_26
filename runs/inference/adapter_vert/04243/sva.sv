property ClockSynceotid; @(posedge clk_in_17) (S) == (1) && (A1) != (A0) ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_17) (S) != 1 && (A0) != (A1) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_17) (S) != 1 && (A1) != (A0) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_17) (S) == 1 && (A0) != (A1) ; endproperty 
 