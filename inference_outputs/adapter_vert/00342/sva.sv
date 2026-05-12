property LoadSynceotid; @(posedge clk) (parallel_load) |-> shift_reg == data_in ;endproperty 
 
 property ShiftIneotid; @(posedge clk) ( !parallel_load ) && (  shift_dir  ) |-> shift_reg == {shift_reg[6:0], 1'b0} ;endproperty 
 
 property ShiftOuteotid; @(posedge clk) ( !parallel_load ) &&  ( !shift_dir )  |-> shift_reg == {1'b0, shift_reg[7:1]} ;endproperty 
 
 property SyncOuteotid; @(posedge clk)  ( serial_out ) == ( shift_reg[0] ) ;endproperty 
 
 property SyncDataeotid; @(posedge clk)  ( parallel_out ) == ( shift_reg ) ;endproperty 
 