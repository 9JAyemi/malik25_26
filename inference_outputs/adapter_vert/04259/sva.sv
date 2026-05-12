property AddOneeotid; @(posedge clk_in_1) (A) |-> (S) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (B) |-> (S) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (CIN) |-> (S) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (B) &&  (CIN) |-> (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (B) &&  ! (CIN) |-> ! (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  ! (B) &&  (CIN) |-> ! (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) ! (A) &&  (B) &&  (CIN) |-> ! (COUT) ;endproperty 
 