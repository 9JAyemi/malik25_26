property MinValideotid; @(posedge clk_in_1) (in) |-> (min) == (in[0]); endproperty 
 
 property MaxValideotid; @(posedge clk_in_1) (in) |-> (max) == (in[0]); endproperty 
 
 property MinMaxeotid; @(posedge clk_in_1) (in) != 6'bxxxxxx |-> (min) != (max); endproperty 
 