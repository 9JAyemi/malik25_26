property AddOneeotid; @(posedge clk_in_19) (opcode) == (3'b000) |-> (out) == (A + B) ; endproperty 
 
 property SubOneeotid; @(posedge clk_in_19) (opcode) == (3'b001) |-> (out) == (A - B) ; endproperty 
 
 property ANDeotid; @(posedge clk_in_19) (opcode) == (3'b010) |-> (out) == (A & B) ; endproperty 
 
 property OReotid; @(posedge clk_in_19) (opcode) == (3'b011) |-> (out) == (A | B) ; endproperty 
 
 property XOrEeotid; @(posedge clk_in_19) (opcode) == (3'b100) |-> (out) == (A ^ B) ; endproperty 
 
 property ShiftLeftOneeotid; @(posedge clk_in_19) (opcode) == (3'b101) |-> (out) == (A << 1) ; endproperty 
 
 property ShiftRightOneeotid; @(posedge clk_in_19) (opcode) == (3'b110) |-> (out) == (A >> 1) ; endproperty 
 
 property NotAeotid; @(posedge clk_in_19) (opcode) == (3'b111) |-> (out) == (~A) ; endproperty 
 
 property ZeroCheckeotid; @(posedge clk_in_19) (out) == 4'b0000 |-> (zero) == 1'b1 ; endproperty 
 
 property Safeeotid; @(posedge clk_in_19) (out) != 4'b0000 |-> (zero) == 1'b0 ; endproperty 
 