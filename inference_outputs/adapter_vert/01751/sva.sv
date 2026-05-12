property ClockSynceotid; @(posedge clk) (clk) |-> (active) == (active_q) ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (clk) &&  (  ! ( clk ) &&  (  active ) ) |->  (  clk_gated )  ;endproperty 
 