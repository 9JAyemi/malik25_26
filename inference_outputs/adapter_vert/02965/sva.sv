property SyncEqeotid; @(posedge clk_in_1) (A) == (B) |-> (C) == 2'b00 ; endproperty 
 
 property SyncGoeotid; @(posedge clk_in_1) (A) != (B) && (A) > (B) |-> (C) == 2'b01 ; endproperty 
 
 property SyncLoadeotid; @(posedge clk_in_1) (A) != (B) && !(A) > (B)  |-> (C) == 2'b10; endproperty 
 