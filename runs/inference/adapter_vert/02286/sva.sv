property ClockSynceotid; @(posedge clk) (d0) |-> (d0_1_24) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk) (d1) |-> (d1_1_27) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk) (d0) ||  (d1) |-> (fully_2_1_bit) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk) (d0) ||  (d1) |-> (y) ; endproperty 
 