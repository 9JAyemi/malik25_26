property SyncCheckeotid; @(posedge clk_in_14) (A1) && (A2) && (A3) |-> and0_out ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_14) (B1) && (B2) |-> and1_out ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_14) (and0_out) || (and1_out) |-> or0_out_X ;endproperty 
 
 property ValidXeotid; @(posedge clk_in_14) (or0_out_X) |->  (X)  ;endproperty 
 