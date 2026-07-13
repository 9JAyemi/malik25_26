property AddOneeotid; @(posedge clk_in_1) (A) |-> (COUT) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (B) |-> (COUT) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (B)  &&  (CIN) |-> (COUT) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (B)  &&  (!CIN)  ||  (A) &&  (!B)  &&  (CIN)  ||  (!A) &&  (B)  &&  (CIN) |-> (SUM) ; endproperty 
 