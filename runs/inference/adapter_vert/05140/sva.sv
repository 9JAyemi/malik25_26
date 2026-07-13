property AddOneeotid; @(posedge clk_in_1) (A) |-> (S) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (B) |-> (S) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (CI) |-> (S) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (CI) |-> (carry_out) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (!CI) |-> (carry_out) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (A) &&  (!B) &&  (CI) |-> (carry_out) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (A) &&  (!B) &&  (!CI) |->  (S)  &&  ( !carry_out) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (!A) &&  (B) &&  (CI) |->  (S)  &&  ( !carry_out) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (!A) &&  (B) &&  (!CI) |-> (carry_out) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (!A) &&  (!B) &&  (CI) |->  (S)  &&  ( !carry_out) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (!A) &&  (!B) &&  (!CI) |->  (S)  &&  ( !carry_out) ;endproperty 
 