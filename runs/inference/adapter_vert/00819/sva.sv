property ValidIneotid; @(posedge clk_in_1) (A) && (B) && (C) |-> X1 ;endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (C) && (D) |-> X2 ;endproperty 
 
 property ValidXeotid; @(posedge clk_in_1) (X1) && (X2)  |->  (X) ;endproperty 
 