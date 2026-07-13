property AddOneeotid; @(posedge clk_in_1) (op) == (2'b00) |-> result == a + b ; endproperty 
 
 property SubOneeotid; @(posedge clk_in_1) (op) == (2'b01) |-> result == a - b ; endproperty 
 
 property Multeotid; @(posedge clk_in_1) (op) == (2'b10) |-> (temp) == (a * b) && ( (temp) > 8'hFF ) |-> result == 8'hFF ; endproperty 
 
 property ValidDivideeotid; @(posedge clk_in_1) (op) == (2'b10) &&  ( !( (temp) > 8'hFF )  && ( (b) != 8'h00 ) )  |-> (temp) == (a / b) && ( (temp) > 8'hFF ) |-> result == 8'hFF ; endproperty 
 
 property ValidDivideeotid; @(posedge clk_in_1) (op) == (2'b10) &&  ( !( (temp) > 8'hFF )  && ( (b) != 8'h00 ) )  |-> (temp) == (a / b) &&  ( (temp) <= 8'hFF )  |-> result == (temp) ; endproperty 
 
 property SafeDivideeotid; @(posedge clk_in_1) (op) == (2'b11) &&  ( (b) == 8'h00 )  |-> result == 8'hFF ; endproperty 
 