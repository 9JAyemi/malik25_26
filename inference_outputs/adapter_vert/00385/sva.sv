property SyncCheckeotid; @(posedge clk_in_15) (A2) != (A1) |-> (nand0_out) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_15) (B2) != (B1) |-> (nand1_out) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_in_15) (nand0_out) && @(posedge clk_in_15) (nand1_out) |-> (and0_out_Y) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_15) (and0_out_Y) |-> ! (and1_out_Y) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_15)  (and1_out_Y)  |->  (Y)  ;endproperty 
 