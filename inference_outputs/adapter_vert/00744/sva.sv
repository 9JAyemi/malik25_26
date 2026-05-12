property AddOneeotid; @(posedge clk_in_1) (op) == (4'b0000) |-> (Y) == (A + B) ; endproperty 
 
 property SubOneeotid; @(posedge clk_in_1) (op) == (4'b0001) |-> (Y) == (A - B) ; endproperty 
 
 property AndOneeotid; @(posedge clk_in_1) (op) == (4'b0010) |-> (Y) == (A & B) ; endproperty 
 
 property OrOneeotid; @(posedge clk_in_1) (op) == (4'b0011) |-> (Y) == (A | B) ; endproperty 
 
 property XorOneeotid; @(posedge clk_in_1) (op) == (4'b0100) |-> (Y) == (A ^ B) ; endproperty 
 
 property NotOneeotid; @(posedge clk_in_1) (op) == (4'b0101) |-> (Y) == (notA) ; endproperty 
 
 property ShiftLeftOneeotid; @(posedge clk_in_1) (op) == (4'b0110) |-> (Y) == (shiftLeft) ; endproperty 
 
 property ShiftRightOneeotid; @(posedge clk_in_1) (op) == (4'b0111) |-> (Y) == (shiftRight) ; endproperty 
 
 property RotateLeftOneeotid; @(posedge clk_in_1) (op) == (4'b1000) |-> (Y) == (rotateLeft) ; endproperty 
 
 property RotateRightOneeotid; @(posedge clk_in_1) (op) == (4'b1001) |-> (Y) == (rotateRight) ; endproperty 
 
 property ValidOpseotid; @(posedge clk_in_1) (op) != 4'bxxxx  |-> (Y) != 16'b0; endproperty 
 