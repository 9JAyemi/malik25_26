property ClockSynceotid; @(posedge clk_osc_19) (A1) == (B1) && (A2) == (B2) |-> (X) == 1'b1 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_19) (C1) == (VPWR) && (VPB) == (VGND) |-> (X) != 1'b1 ;endproperty 
 