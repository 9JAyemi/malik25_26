property LoadSynceotid; @(posedge clk) (load) |-> shift_reg == data ;endproperty 
 
 property ValidDataeotid; @(posedge clk) ( !load ) &&  (  ena != 2'b00 ) |-> shift_reg == data ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) ( !load )  &&  (  !(ena != 2'b00)  )  |-> out_if_else == 1'b0 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) ( !load )  &&  (  !(ena != 2'b00)  )  |-> q == shift_reg ;endproperty 
 