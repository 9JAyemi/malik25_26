property ClockSynceotid; @(posedge clk) ( d ) |-> reg_data == {reg_data[1:0], d} ;endproperty 
 
 property SyncRsteotid; @(posedge clk) ( d ) |-> q == reg_data[0] ;endproperty 
 