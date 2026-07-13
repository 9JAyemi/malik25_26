property SyncCheckeotid; @(posedge clk_in_13) (Y) |-> (and0_out) && (and1_out) && (and2_out) && (nor0_out_Y);endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_13) (and0_out) && (and1_out) && (and2_out) |-> (Y) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_13) (and1_out) && (and2_out) |-> (nor0_out_Y); endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_13) (and0_out) && (and1_out) && (and2_out) && (nor0_out_Y) |-> (Y); endproperty 
 