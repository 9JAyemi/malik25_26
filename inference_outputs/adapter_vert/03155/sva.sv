property AddOneeotid; @(posedge clk) (cos) == (one) && (s2) |-> (add1) == (cos + one); endproperty 
 
 property ValidXeotid; @(posedge clk) (cos) == (one) && (s2) |-> (x2) == (add1 * s2); endproperty 
 
 property ValidXeotid; @(posedge clk) (cos) == (one) && (s2) |-> (x3) == (cos * s1); endproperty 
 
 property ValidSumeotid; @(posedge clk) (cos) == (one) && (s2) |-> (s1_out) == (x2 + x3); endproperty 
 
 property ValidSubeotid; @(posedge clk) (cos) != (one) && (s1) |-> (sub5) == (one - cos); endproperty 
 
 property ValidXeotid; @(posedge clk) (cos) != (one) && (s1) |-> (x6) == (sub5 * s1); endproperty 
 
 property ValidXeotid; @(posedge clk) (cos) != (one) && (s1) |-> (x7) == (cos * s2); endproperty 
 
 property ValidSumeotid; @(posedge clk) (cos) != (one) && (s1) |-> (s2_out) == (x6 + x7); endproperty 
 