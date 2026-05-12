property ResetSynceotid; @(posedge clk) (rst) |-> data_sync == 2'b00 ;endproperty 
 
 property SyncIneotid; @(posedge clk) (rst) != 1'b1  |-> data_sync == {data_sync[0], data_in} ;endproperty 
 
 property SyncDataeotid; @(posedge clk) (rst) != 1'b1  |-> data_out == data_sync[1] ;endproperty 
 