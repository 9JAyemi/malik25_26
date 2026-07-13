property ClockSynceotid; @(posedge clk_in_19) (TE_B) |-> (Z) == 1'b0 ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_19) (TE_B) |-> (A) == 1'b0 ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_19) ! (TE_B)  |-> (Z) ==  (A) ; endproperty 
 