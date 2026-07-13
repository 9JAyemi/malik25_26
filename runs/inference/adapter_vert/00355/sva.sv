property ResetSynceotid; @(posedge w_clock) (w_reset) |-> r_bus_addr_out == 8'b0 ;endproperty 
 
 property SyncLoadeotid; @(posedge w_clock) (w_reset) != 1'b1  |-> r_bus_addr_out == w_bus_addr_in; endproperty 
 