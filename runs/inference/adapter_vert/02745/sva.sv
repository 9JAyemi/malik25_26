property AddOneeotid; @(posedge clk_in_1) (A) |-> (S) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (B) |-> (S) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (CI) |-> (S) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (B) &&  (CI) |-> (CO) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (B) &&  (!CI) |-> !(CO) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (!B) &&  (CI) |-> !(CO) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (!A) &&  (B) &&  (CI) |-> !(CO) ;endproperty 
 