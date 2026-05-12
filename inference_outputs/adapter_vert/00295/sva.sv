property AddOneeotid; @(posedge clk_in_1) (opcode) == (3'b000) |-> (out) == (A + B) ; endproperty 
 
 property SubOneeotid; @(posedge clk_in_1) (opcode) == (3'b001) |-> (out) == (A - B) ; endproperty 
 
 property ANDeotid; @(posedge clk_in_1) (opcode) == (3'b010) |-> (out) == (A & B) ; endproperty 
 
 property OReotid; @(posedge clk_in_1) (opcode) == (3'b011) |-> (out) == (A | B) ; endproperty 
 
 property XorOneeotid; @(posedge clk_in_1) (opcode) == (3'b100) |-> (out) == (A ^ B) ; endproperty 
 
 property Zeroeotid; @(posedge clk_in_1) (result) == (4'b0000) |-> (zero) == 1'b1 ; endproperty 
 