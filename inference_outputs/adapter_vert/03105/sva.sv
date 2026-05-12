property BitwiseAndeotid; @(posedge clk_in_1) (sel) == (2'b00) |-> (out) == (A & B) ; endproperty 
 
 property BitwiseOrEeotid; @(posedge clk_in_1) (sel) == (2'b01) |-> (out) == (A | B) ; endproperty 
 
 property BitwiseXorEeotid; @(posedge clk_in_1) (sel) == (2'b10) |-> (out) == (A ^ B) ; endproperty 
 
 property ValidXorOuteotid; @(posedge clk_in_1) (sel) == (2'b11) |-> (out) == (~(A ^ B)) ; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_1) (sel) != 2'b00 && @(posedge clk_in_1) (sel) != 2'b01 && @(posedge clk_in_1) (sel) != 2'b10 && @(posedge clk_in_1) (sel) != 2'b11  |-> (out) == 4'b0; endproperty 
 