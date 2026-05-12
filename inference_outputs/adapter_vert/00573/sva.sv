property ClockSafeeotid; @(posedge clk_osc_19) (Y) |-> ! ( A ) && ! ( B ) && ! ( C ) &&  ( D_N ) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) (Y) |->  ( A ) ||  ( B ) ||  ( C ) || ! ( D_N ) ;endproperty 
 
 property ClockSafeeotid; @(posedge clk_osc_19) (Y) |->  ( A ) &&  ( B ) &&  ( C ) && ! ( D_N ) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) (Y) |-> ! ( A ) &&  ( B ) &&  ( C ) && ! ( D_N ) ;endproperty 
 