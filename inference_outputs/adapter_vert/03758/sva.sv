property ResetSynceotid; @(posedge clk) (rst_n) |-> (nxt_state) == (5'h0) ; endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst_n) |-> (cur_state) == (5'b1) ; endproperty 
 
 property ValidAckeotid; @(posedge clk) (rst_n) &&  (  (cur_state) == (5'b1)  &&  (nxt_state) == (5'h1)  ) |->  (ack) == 1'b1 ; endproperty 
 
 property ValidStateeotid; @(posedge clk) (rst_n) &&  (  (cur_state) != 5'b1  ||  (nxt_state) != 5'h1  ) |->  (ack) != 1'b1 ; endproperty 
 
 property SyncStateeotid; @(posedge clk) (rst_n) |-> (nxt_state) == (cur_state) ; endproperty 
 
 property SyncStateeotid; @(posedge clk) (rst_n) &&  (  (cur_state) != 5'b1  ||  (nxt_state) != 5'h1  ) |->  (cur_state) != 5'b1 ; endproperty 
 
 property SyncStateeotid; @(posedge clk) (rst_n) &&  (  (cur_state) != 5'b1  ||  (nxt_state) != 5'h1  ) &&  (  (cur_state) != 5'b1  ||  (nxt_state) != 5'h1  ) |->  (nxt_state) != 5'h1 ; endproperty 
 