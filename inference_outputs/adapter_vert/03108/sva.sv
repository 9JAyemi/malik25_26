property ResetSynceotid; @(posedge clk) (reset) |-> (d_ff_1 == 1'b0) && (d_ff_2 == 1'b0) ;endproperty 
 
 property SyncIneotid; @(posedge clk) ( !reset ) |-> (d_ff_1 == d_in) && (d_ff_2 == toggle) ;endproperty 
 
 