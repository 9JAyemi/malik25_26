property SyncAdderCheckeotid; @(posedge clk_in_13) (CTRL) == (0) |-> (C) == (A + B) ; endproperty 
 
 property SyncAddereotid; @(posedge clk_in_13) (CTRL) != 0 |-> (C) == ({1'b0, A[3:1]} + {1'b0, B[3:1]}); endproperty 
 