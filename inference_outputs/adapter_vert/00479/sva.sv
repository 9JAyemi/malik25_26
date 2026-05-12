property SyncCheckeotid; @(posedge clk_signal_1) (A) && (B) |-> (and0_out_COUT) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_signal_1) (A) && (B) |-> (COUT) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_signal_1) (B) != (A) |-> (xor0_out_SUM) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_signal_1) (B) != (A) |-> (SUM) ;endproperty 
 