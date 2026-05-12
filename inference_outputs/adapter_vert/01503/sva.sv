property ClockSynceotid; @(posedge clk) (in) &&  ( !d_last ) |-> state == COUNT ;endproperty 
 property ClockSynceotid; @(posedge clk) (in) &&  ( !d_last ) &&  (  count != 4 ) |-> count == (count + 1) ;endproperty 
 property SyncReseteotid; @(posedge clk) (in) &&  ( !d_last ) &&  (  count == 4 ) |-> state == IDLE ;endproperty 
 property SyncCheckeotid; @(posedge clk)  (  !in )  |-> state == IDLE ;endproperty 
 