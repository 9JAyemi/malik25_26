property SyncIneotid; @(posedge clk_in_15) (D) |-> (nand0_out) ;endproperty 
 
 property SyncIneotid; @(posedge clk_in_15) (B_N) && (A_N) &&  (C) |-> (or0_out_Y) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_in_15) (or0_out_Y)  |-> (Y) ;endproperty 
 