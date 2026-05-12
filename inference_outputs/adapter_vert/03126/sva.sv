property ResetSynceotid; @(posedge clk) (reset) |-> (prev_state == 0) && (out == 0) ;endproperty 
 
 property SyncIneotid; @(posedge clk) ( !reset ) |-> ( prev_state == in ) && ( out == (in & ~prev_state) ) ;endproperty 
 