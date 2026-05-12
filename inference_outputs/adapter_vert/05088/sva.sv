property SyncAdderCheckeotid; @(posedge clk_in_14) (CIN) |-> (ci) ; endproperty 
 
 property ValidAddereotid; @(posedge clk_in_14) (A) != (B) && (CIN) |-> (xor0_out_SUM) ; endproperty 
 
 property ValidAddereotid; @(posedge clk_in_14) (A) != (B) && ! (CIN)  |-> (xor0_out_SUM) ; endproperty 
 
 property ValidAddereotid; @(posedge clk_in_14) (A) == (B) && (CIN) |-> (or0_out_COUT) ; endproperty 
 
 property ValidAddereotid; @(posedge clk_in_14) (A) == (B) && ! (CIN)  |-> (or0_out_COUT) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_14) (A) != (B) && (CIN) |-> (xor0_out_SUM) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_14) (A) != (B) && ! (CIN)  |-> (xor0_out_SUM) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_14) (A) == (B) && (CIN) |-> (or0_out_COUT) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_14) (A) == (B) && ! (CIN)  |-> (or0_out_COUT) ; endproperty 
 
 