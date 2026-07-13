property AdderSynceotid; @(posedge clk_in_1) (A) |-> (temp_sum) == (A + B + Cin); endproperty 
 
 property ValidSumeotid; @(posedge clk_in_1) (A) &&  (B) &&  (Cin) |-> (Sum) == (temp_sum[3:0]); endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (Cin) |-> (Cout) == (temp_sum[4]); endproperty 
 