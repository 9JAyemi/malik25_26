property ClockSynceotid; @(posedge clk_osc_19) (X) |-> (or0_out) && (and0_out_X); endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) (or0_out) &&  (  (A2) || (A1)  ) &&  (  (or0_out) && (and0_out_X)  ) |-> (X) == (and0_out_X); endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) (or0_out) &&  (  (A2) || (A1)  ) &&  (  !(or0_out) || !(and0_out_X)  ) |-> (X) != (and0_out_X); endproperty 
 