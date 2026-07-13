property SyncIneotid; @(posedge clk) (synch_in) |-> (synch_d) ;endproperty 
 
 property SyncFloweotid; @(posedge clk) (synch_in) &&  (  (C_NUM_STAGES)  != 0 ) |-> (synch_d) ;endproperty 
 
 property SyncFloweotid; @(posedge clk) (synch_in) &&  (  (C_NUM_STAGES)  != 0 ) &&  (  (C_NUM_STAGES)  != 1 )  |-> (synch_d) ;endproperty 
 
 property SyncFloweotid; @(posedge clk) (synch_in) &&  (  (C_NUM_STAGES)  != 0 ) &&  (  (C_NUM_STAGES)  != 1 ) &&  (  (C_NUM_STAGES)  != 2 )  |-> (synch_out) == (synch_d) ;endproperty 
 
 