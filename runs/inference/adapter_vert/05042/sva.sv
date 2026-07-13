property MinAeotid; @(posedge clk_in_1) (a) < (b) |-> (ab_min) == (a) ; endproperty 
 
 property MinCdeotid; @(posedge clk_in_1) (c) < (d) |-> (cd_min) == (c) ; endproperty 
 
 property MinValideotid; @(posedge clk_in_1) (ab_min) < (cd_min) |-> (abcd_min) == (ab_min) ; endproperty 
 
 property MinValideotid; @(posedge clk_in_1) (a) < (b) && (c) < (d)  |-> (min) == (ab_min) ; endproperty 
 