property ClockSynceotid; @(posedge clk_osc_19) (A1) != (A2) |-> (X) == (a1_xored_a2 & B1); endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_19) (A1) && (A2) == (b1_bit0) ; endproperty 
 