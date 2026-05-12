property OneComplementeotid; @(posedge clk_in_13) (a) |-> (ones_comp) == (~a) ;endproperty 
 
 property Inverseeotid; @(posedge clk_in_13) (a) |-> (inverted) == (ones_comp + 4'b1) ;endproperty 
 
 property TwoComplementeotid; @(posedge clk_in_13) (a) |-> (add_one) == (inverted + 4'b1) &&  (  inverted[3]  ) ;endproperty 
 
 property TwoComplementeotid; @(posedge clk_in_13) (a) |-> (twos_comp) == (add_one) ;endproperty 
 