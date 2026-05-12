property ResetSynceotid; @(posedge clk) (rst) |-> (out_send == 0) ;endproperty 
 
 property SyncRxeotid; @(posedge clk) (rst) != 1'b1 |-> (out_send == in_receive) ;endproperty 
 