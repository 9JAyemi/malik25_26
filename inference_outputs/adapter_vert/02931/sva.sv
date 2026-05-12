property GreaterThaneotid; @(posedge clk_in_13) (a) > (b) |-> (gt) == 1'b1 && (lt) == 1'b0 && (eq) == 1'b0 ;endproperty 
 
 property LessThaneotid; @(posedge clk_in_13) (a) < (b) |-> (gt) == 1'b0 && (lt) == 1'b1 && (eq) == 1'b0 ;endproperty 
 
 property EqualToeotid; @(posedge clk_in_13) (a) == (b) |-> (gt) == 1'b0 && (lt) == 1'b0 && (eq) == 1'b1 ;endproperty 
 