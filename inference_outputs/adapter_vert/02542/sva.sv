property SyncCheckeotid; @(posedge clk_osc_11) (A_N) && (  B ) |->  ! ( Y ) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_11) (A_N) || (  B ) |->  ( Y ) ;endproperty 
 