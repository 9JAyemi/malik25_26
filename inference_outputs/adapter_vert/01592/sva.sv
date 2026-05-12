property AdderSynceotid; @(posedge clk_in_14) (A) |-> (SUM) == (A ^ B ^ CI); endproperty 
 
 property CarrySynceotid; @(posedge clk_in_14) (A) &&  (B) &&  (CI) |-> (COUT) == 1'b1 ; endproperty 
 
 property CarrySynceotid; @(posedge clk_in_14) (A) &&  (B) &&  (!CI) ||  (A) &&  (!B) &&  (CI) ||  (!A) &&  (B) &&  (CI)  |-> (COUT) == 1'b1 ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_14) (B) |-> (SUM) == (A ^ B ^ CI); endproperty 
 
 property CarrySynceotid; @(posedge clk_in_14) (B) &&  (CI) |-> (COUT) == 1'b1 ; endproperty 
 
 property CarrySynceotid; @(posedge clk_in_14) (B) &&  (A) &&  (!CI) ||  (B) &&  (!A) &&  (CI)  |-> (COUT) == 1'b1 ; endproperty 
 