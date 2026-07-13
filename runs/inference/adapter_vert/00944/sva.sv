property ClockSynceotid; @(posedge clk_in_1) (S) == (0) |-> (X) == (A0) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (S) == (1) |-> (X) == (A1) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (S) != 0 && @(posedge clk_in_1) (S) != 1 |-> (X) == 1'bx ; endproperty 
 