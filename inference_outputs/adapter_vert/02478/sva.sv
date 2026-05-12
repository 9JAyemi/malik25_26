property SyncUpeotid; @(posedge clk) (up_down) |-> (q != 7) ; endproperty 
 
 property SyncDowneotid; @(posedge clk) (up_down) &&  (q == 7) |-> (q == 0) ; endproperty 
 
 property SyncUpeotid; @(posedge clk) ! (up_down)  &&  (q != 7) |-> (q == data_14) ; endproperty 
 
 property SyncDowneotid; @(posedge clk) ! (up_down)  &&  (q == 7) |-> (q == 6) ; endproperty 
 