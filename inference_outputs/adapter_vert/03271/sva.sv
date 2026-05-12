property AddOneeotid; @(posedge clk_in_1) (alu_ctl) == (4'b0001) |-> result == A + B ; endproperty 
 
 property SubOneeotid; @(posedge clk_in_1) (alu_ctl) == (4'b0010) |-> result == A - B ; endproperty 
 
 property AndOneeotid; @(posedge clk_in_1) (alu_ctl) == (4'b0011) |-> result == A & B ; endproperty 
 
 property OrOneeotid; @(posedge clk_in_1) (alu_ctl) == (4'b0100) |-> result == A | B ; endproperty 
 
 property XorOneeotid; @(posedge clk_in_1) (alu_ctl) == (4'b0101) |-> result == A ^ B ; endproperty 
 
 property NotOrOneeotid; @(posedge clk_in_1) (alu_ctl) == (4'b0110) |-> result == ~(A | B) ; endproperty 
 
 property RightShifteotid; @(posedge clk_in_1) (alu_ctl) == (4'b0111) |-> result == B >> 1 ; endproperty 
 
 property ZeroCheckeotid; @(posedge clk_in_1) (alu_ctl) == (4'b1000) |-> result == {B[15:0], 16'b0} ; endproperty 
 
 property LessThaneotid; @(posedge clk_in_1) (alu_ctl) == (4'b1001) |-> result == (A < B) ; endproperty 
 
 property ZeroCheckeotid; @(posedge clk_in_1) (alu_ctl) != 4'b0001 && @(posedge clk_in_1) (alu_ctl) != 4'b0010 && @(posedge clk_in_1) (alu_ctl) != 4'b0011 && @(posedge clk_in_1) (alu_ctl) != 4'b0100 && @(posedge clk_in_1) (alu_ctl) != 4'b0101 && @(posedge clk_in_1) (alu_ctl) != 4'b0110 && @(posedge clk_in_1) (alu_ctl) != 4'b0111 && @(posedge clk_in_1) (alu_ctl) != 4'b1000 && @(posedge clk_in_1) (alu_ctl) != 4'b1001  |-> result == 0; endproperty 
 