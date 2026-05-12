property SyncIneotid; @(posedge clk_in_14) (X) != (A1_N) && (A2_N); endproperty 
 
 property SyncIneotid; @(posedge clk_in_14) (B1) != (B2); endproperty 
 
 property SyncIneotid; @(posedge clk_in_14) (A1_N) != (B2); endproperty 
 
 property SyncIneotid; @(posedge clk_in_14) (A2_N) != (B1); endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_14) (X) != (A1_N) && (A2_N) && (B1) != (B2); endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_14) (X) != (A1_N) && (A2_N) && (A1_N) != (B2); endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_14) (X) != (A1_N) && (A2_N) && (A2_N) != (B1); endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_14) (X) != (A1_N) && (A2_N) && (B1) != (B2) && (A1_N) != (B2) && (A2_N) != (B1); endproperty 
 
 