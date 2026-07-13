property SyncIneotid; @(posedge clk_in_14) (A) && (B) |-> (AB); endproperty 
 
 property SyncIneotid; @(posedge clk_in_14) (C) && (D) |-> (CD); endproperty 
 
 property ValidSynceotid; @(posedge clk_in_14) (AB) && (CD) |-> (ABCD); endproperty 
 
 property ValidSynceotid; @(posedge clk_in_14) (ABCD) |-> ! (X); endproperty 
 