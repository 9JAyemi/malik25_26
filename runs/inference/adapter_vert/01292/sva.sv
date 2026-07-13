property ResetSynceotid; @(posedge clk) (in) == (1'b0) && (state == state0) |-> next_state == state0 ; endproperty 
 
 property SyncCheckeotid; @(posedge clk) (in) != 1'b0 && (state == state0) |-> next_state == state1 ; endproperty 
 
 property SyncCheckeotid; @(posedge clk) (in) == 1'b0 && (state == state1) |-> next_state == state0 ; endproperty 
 
 property SyncSafeeotid; @(posedge clk) (in) != 1'b0 && (state == state1) |-> next_state == state2 ; endproperty 
 
 property SyncSafeeotid; @(posedge clk) (in) == 1'b0 && (state == state2) |-> next_state == state0 ; endproperty 
 
 property SyncSafeeotid; @(posedge clk) (in) != 1'b0 && (state == state2) |-> next_state == state2 ; endproperty 
 
 property SyncSafeeotid; @(posedge clk)  (state) == state0  |->  (out) == 1'b0 ; endproperty 
 
 property ResetSynceotid; @(posedge clk)  (state) != state0  |->  (out) != 1'b1 ; endproperty 
 