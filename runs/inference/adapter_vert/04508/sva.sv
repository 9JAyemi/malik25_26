property BitwiseORorLogicalOR; @(posedge clk_in_1) (a) |-> (or_bitwise) ; endproperty 
 
 property ORorORorOR; @(posedge clk_in_1) (a) && (b) |-> (or_logical) ; endproperty 
 
 property NotAorNotB; @(posedge clk_in_1) (a) |-> (not_a) ; endproperty 
 
 property NotAorNotBorNotBoth; @(posedge clk_in_1) (b) |-> (not_b) ; endproperty 
 
 property NotAandNotB; @(posedge clk_in_1) (a) && (b) |-> (out_not) ; endproperty 
 