property ResetSynceotid; @(posedge clk) (rst) |-> (q == 4'b0) && (carry == 1'b0) ;endproperty 
 
 property SyncUpeotid; @(posedge clk) (rst) != 1'b1 &&  (up_down == 1'b0)  |->  (q == 4'b1111) &&  (carry == 1'b1)  ;endproperty 
 
 property SyncDowneotid; @(posedge clk) (rst) != 1'b1 &&  (up_down != 1'b0)  |->  (q == 4'b0000) &&  (carry == 1'b1)  ;endproperty 
 
 property SyncCtrleotid; @(posedge clk) (rst) != 1'b1 &&  (up_down != 1'b0)  &&  (q != 4'b0000)  |->  (q == 4'b1111) ;endproperty 
 
 property SyncDowneotid; @(posedge clk) (rst) != 1'b1 &&  (up_down == 1'b0)  &&  (q != 4'b1111)  |->  (q == 4'b0000) ;endproperty 
 