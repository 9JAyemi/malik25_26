property ClockSynceotid; @(posedge clock_div_19) (COUT) |-> (and0_out_COUT) ;endproperty 
 
 property ClockSynceotid; @(posedge clock_div_19) (and0_out_COUT) |-> (COUT) ;endproperty 
 
 property SyncCheckeotid; @(posedge clock_div_19) (B) != (A) |-> (xor0_out_SUM) ;endproperty 
 
 property SyncCheckeotid; @(posedge clock_div_19) (xor0_out_SUM) |-> (SUM) ;endproperty 
 