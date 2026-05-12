property ValidDataeotid; @(posedge clk_in_1) (sel1) && (sel2) |-> (out) == (d3) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (sel1) && (!sel2) |-> (out) == (d2) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (!sel1) && (sel2) |-> (out) == (d1) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (!sel1) && (!sel2) |-> (out) == (d0) ; endproperty 
 