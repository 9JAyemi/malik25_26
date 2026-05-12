property ClockSynceotid; @(posedge clk) (ctr_q) |-> ctr_d == ctr_q + 1'b1 ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (ctr_q) &&  (  rst == 1 ) |-> ctr_q == 'b0 ;endproperty 
 
 property SyncCtrleotid; @(posedge clk) (ctr_q) &&  (  rst != 1 )  |-> ctr_q == ctr_d ;endproperty 
 