property ResetSynceotid; @(posedge clk_i) (reset_n) |-> (state) == (S0) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_i) (reset_n) |-> (state) == (state_next) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_i) (reset_n) |-> (sel) == 3'b000 ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_i) (reset_n) &&  (  (state) == (S0)  ) |-> (state_next) == (S1) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_i) (reset_n) &&  (  (state) == (S1)  ) |-> (state_next) == (S2) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_i) (reset_n) &&  (  (state) == (S2)  ) |-> (state_next) == (S3) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_i) (reset_n) &&  (  (state) == (S3)  ) |-> (state_next) == (S0) ; endproperty 
 