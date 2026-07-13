property AddSynceotid; @(posedge clk_in_1) (B) |-> (B_INV) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (SUB) |-> (ADD) ;endproperty 
 
 property ValidOuteotid; @(posedge clk_in_1) (SUB) |-> (OUT) ;endproperty 
 
 property ValidOuteotid; @(posedge clk_in_1) (SUB) |-> (COUT) ;endproperty 
 
 property SyncAddOneeotid; @(posedge clk_in_1) (B) != (B_INV) ;endproperty 
 
 property SyncAddOneeotid; @(posedge clk_in_1) (SUB) != (ADD) ;endproperty 
 
 property SyncAddOneeotid; @(posedge clk_in_1) (SUB) != (OUT) ;endproperty 
 
 property SyncAddOneeotid; @(posedge clk_in_1) (SUB) != (COUT) ;endproperty 
 