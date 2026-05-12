property AddOneeotid; @(posedge clk_in_1) (op) == (2'b00) |-> result == A + B ; endproperty 
 
 property SubOneeotid; @(posedge clk_in_1) (op) == (2'b01) |-> result == A - B ; endproperty 
 
 property MultOneeotid; @(posedge clk_in_1) (op) == (2'b10) |-> result == A * B ; endproperty 
 
 property SafeDivideeotid; @(posedge clk_in_1) (op) == (2'b11) && (B != 7'b0000000) |-> result == A / B ; endproperty 
 
 property SafeDivideeotid; @(posedge clk_in_1) (op) == (2'b11) && (B == 7'b0000000) |-> result == 0 ; endproperty 
 