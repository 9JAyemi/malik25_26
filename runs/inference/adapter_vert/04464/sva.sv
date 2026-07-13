property AddOneeotid; @(posedge clk_in_1) (A) + (B) == (S) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) + (B) > 4'b1111 |-> (C) ;endproperty 
 
 property CarryOneeotid; @(posedge clk_in_1) (A) + (B) > 4'b1111 |-> (Cout) ;endproperty 
 