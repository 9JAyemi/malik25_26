property ResetSynceotid; @(posedge clk) (reset) |-> result == 0 ;endproperty 
 
 property ValidOnReseteotid; @(posedge clk) ( !reset ) |-> result == ( a * b ) ;endproperty 
 