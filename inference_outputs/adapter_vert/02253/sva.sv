property AddOneeotid; @(posedge clk_in_19) (op) == (3'b000) |-> (out) == (a + b) ; endproperty 
 
 property SubOneeotid; @(posedge clk_in_19) (op) == (3'b001) |-> (out) == (a - b) ; endproperty 
 
 property AndOneeotid; @(posedge clk_in_19) (op) == (3'b010) |-> (out) == (a & b) ; endproperty 
 
 property OrOneeotid; @(posedge clk_in_19) (op) == (3'b011) |-> (out) == (a | b) ; endproperty 
 
 property XorOneeotid; @(posedge clk_in_19) (op) == (3'b100) |-> (out) == (a ^ b) ; endproperty 
 
 property ShiftOneeotid; @(posedge clk_in_19) (op) == (3'b101) |-> (out) == ({a[2:0], 1'b0}) ; endproperty 
 
 property SafeSynceotid; (op) != 3'b000 && (op) != 3'b001 && (op) != 3'b010 && (op) != 3'b011 && (op) != 3'b100 && (op) != 3'b101  |-> (out) == 4'b0 ; endproperty 
 