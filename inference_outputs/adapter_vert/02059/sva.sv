property TwosComplementeotid; @(posedge clk_in_14) (A) |-> (OUT) == (~A + 1) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_14) (sel) |-> (OUT) == (A) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_14) (sel) != 1'b1  |-> (OUT) == (B) ;endproperty 
 