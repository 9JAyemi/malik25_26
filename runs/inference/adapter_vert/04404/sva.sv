property SyncIneotid; @(posedge clk_in_19) (A) && (B) |-> ab ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_19) (B) && (C) |-> bc ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_19) (A) && (C) |-> ac ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_19) (ab) || (bc) || (ac) |-> X ; endproperty 
 
 property PowerSynceotid; @(posedge clk_in_19)  (VGND) == (0) &&  (VPWR) == (1) &&  (VPB) == (1) &&  (VNB) == (0) ; endproperty 
 