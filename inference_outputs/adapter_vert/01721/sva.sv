property SyncIneotid; @(posedge clk_in_1) (A1) && (A2) |-> (temp1) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (A1) && (A2) && (A3) |-> (temp2) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (A1) && (A2) && (A3) && (B1) |-> (temp3) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_1) (A1) && (A2) && (A3) && (B1) && (C1) |-> (Y) ;endproperty 
 