property AdderSynceotid; @(posedge clk_in_19) (A) != (B) |-> (S) != (A); endproperty 
 
 property AdderSynceotid; @(posedge clk_in_19) (A) != (B) |-> (C_out) == (c); endproperty 
 
 property AdderSynceotid; @(posedge clk_in_19) (A) == (B) && (A) != 4'b0000 |-> (S) == 4'b0000 ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_19) (A) == (B) && (A) != 4'b0000 |-> (C_out) == 1'b0 ; endproperty 
 