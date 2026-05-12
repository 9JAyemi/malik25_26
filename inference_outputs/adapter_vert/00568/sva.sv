property AddOneeotid; @(posedge clk_in_12) (alucontrol[0]) |-> (cout) == (srca) && (sum) == (srcbc) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_12) (alucontrol[0]) |-> (aluresult) == (sum) ; endproperty 
 
 property ANDeotid; @(posedge clk_in_12) (alucontrol) == (2'b10) |-> (aluresult) == (srca) && (aluresult) == (srcb) ; endproperty 
 
 property OReotid; @(posedge clk_in_12) (alucontrol) == (2'b11) |-> (aluresult) == (srca) || (aluresult) == (srcb) ; endproperty 
 
 property ValidReseteotid; @(posedge clk_in_12) (alucontrol[0]) |-> (aluflags) == (4'bxx10) ; endproperty 
 
 property ValidReseteotid; @(posedge clk_in_12) (alucontrol[0]) |-> (aluflags) == (4'b0010) ; endproperty 
 
 property ValidReseteotid; @(posedge clk_in_12) (alucontrol[0]) |-> (aluflags) != 4'b0000 ; endproperty 
 