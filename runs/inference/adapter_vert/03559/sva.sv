property ClockSynceotid; @(posedge clk_in_1) (O) |-> (A) ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_1) (O) |-> (B) ; endproperty 
 
 property SyncOuteotid; @(posedge clk_in_1) (O) == (A | B) ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_1) (C) |-> (C) ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_1) (D) |-> (D) ; endproperty 
 
 property SyncOuteotid; @(posedge clk_in_1) (CO) |-> (C) || (D) ; endproperty 
 