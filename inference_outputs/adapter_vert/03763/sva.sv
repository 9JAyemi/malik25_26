property PowerSynceotid; @(posedge clk_in_15) (VPWR) |-> (fill) ;endproperty 
 
 property SafeStarteotid; @(posedge clk_in_15) (VGND) |-> ! (fill) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_15) (VPB) |-> ! (fill) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_15) (VNB) |->  (fill) ;endproperty 
 