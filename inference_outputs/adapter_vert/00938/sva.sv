property AdderSynceotid; @(posedge clk_in_1) (A) |-> (sum) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (Cin) |-> (carry) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (!Cin) |-> (sum) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) ||  (B) ||  (Cin) |-> (carry) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) &&  (!B) &&  (Cin) |-> (sum) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) &&  (!B) &&  (!Cin) |-> (sum) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (!A) &&  (B) &&  (Cin) |-> (sum) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (!A) &&  (B) &&  (!Cin) |-> (sum) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (!A) &&  (!B) &&  (Cin) |-> (carry) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (!A) &&  (!B) &&  (!Cin) |-> (sum) ; endproperty 
 