property ResetSynceotid; @(posedge CLK) (RST) |-> C_reg == 8'b0 ;endproperty 
 
 property SubOnRsteotid; @(posedge CLK) (RST) != 1'b1 &&  (OP) == 1'b1  |-> C_reg == A - B ;endproperty 
 
 property AddOnRsteotid; @(posedge CLK) (RST) != 1'b1 &&  (OP) != 1'b1  |-> C_reg == A + B ;endproperty 
 