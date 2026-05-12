property SyncEqeotid; @(posedge clk_in_13) (A1_N) && (A2_N) &&  (B2) |->  (Y) == 1'b1 ;endproperty 
 
 property SyncEqeotid; @(posedge clk_in_13) (A1_N) &&  (!A2_N) &&  (B1) |->  (Y) == 1'b1 ;endproperty 
 
 property SyncEqeotid; @(posedge clk_in_13)  (!A1_N) && (A2_N) &&  (B2) |->  (Y) == 1'b1 ;endproperty 
 
 property SyncEqeotid; @(posedge clk_in_13)  (!A1_N) &&  (!A2_N) &&  (B1) |->  (Y) == 1'b1 ;endproperty 
 