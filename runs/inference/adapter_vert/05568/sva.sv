property AddOneeotid; @(posedge clk_in_1) (op) == (2'b00) |-> (result) == (num1 + num2) ; endproperty 
 
 property SubOneeotid; @(posedge clk_in_1) (op) == (2'b01) |-> (result) == (num1 - num2) ; endproperty 
 
 property MultOneeotid; @(posedge clk_in_1) (op) == (2'b10) |-> (result) == (num1 * num2) ; endproperty 
 
 property DivOneeotid; @(posedge clk_in_1) (op) == (2'b11) && (  !(num2)  ) |-> (result) == 8'b00000000 ; endproperty 
 
 property SafeDivideeotid; @(posedge clk_in_1) (op) == (2'b11) && (  (num2)  ) |-> (result) == (num1 / num2) ; endproperty 
 