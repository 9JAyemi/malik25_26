property AddOneeotid; @(posedge clk_in_1) (op) == (2'b00) |-> result == a + b ;endproperty 
 
 property SubOneeotid; @(posedge clk_in_1) (op) == (2'b01) |-> result == a - b ;endproperty 
 
 property MultOneeotid; @(posedge clk_in_1) (op) == (2'b10) |-> result == a * b ;endproperty 
 
 property DivOneeotid; @(posedge clk_in_1) (op) == (2'b11) && (b != 0) |-> result == a / b ;endproperty 
 