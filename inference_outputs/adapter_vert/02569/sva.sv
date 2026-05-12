property ValidIneotid; @(posedge clk_in_1) (Y) |-> (w3) && (w2) && (w1) && (A1) && (A2);endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (w3) |-> (w2) && (B1);endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (w2) |-> (w1) && (C1);endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (w1) |-> (Y) && (D1);endproperty 
 