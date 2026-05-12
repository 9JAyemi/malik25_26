property AdderSynceotid; @(posedge clk_in_1) (A) |-> (S) == (sum); endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) &&  (B) |-> (C_out) == (sum[8]); endproperty 
 