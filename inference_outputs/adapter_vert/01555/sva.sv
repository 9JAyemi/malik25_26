property LeftShiftsOnRiseeotid; @(posedge clk_in_1) (dir) == (0) |-> (out) == (in << shift); endproperty 
 
 property RightShiftsOnRiseeotid; @(posedge clk_in_1) (dir) != 0 |-> (out) == (in >> shift); endproperty 
 