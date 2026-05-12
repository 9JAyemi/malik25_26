property AddSynceotid; @(posedge clk_in_1) (ctrl) == (2'b00) |-> result == a + b ; endproperty 
 
 property SubSynceotid; @(posedge clk_in_1) (ctrl) == (2'b01) |-> result == a - b ; endproperty 
 
 property XorSynceotid; @(posedge clk_in_1) (ctrl) == (2'b10) |-> result == a ^ b ; endproperty 
 
 property ValidCtrleotid; @(posedge clk_in_1) (ctrl) != 2'b00 && @(posedge clk_in_1) (ctrl) != 2'b01 && @(posedge clk_in_1) (ctrl) != 2'b10  |-> result == 8'b0; endproperty 
 