property ResetSynceotid; @(posedge clk) (areset) |-> shift_reg == 4'b0 ; endproperty 
 
 property LoadSynceotid; @(posedge clk) (areset) != 1'b1 && (load) |-> shift_reg == data ; endproperty 
 
 property ShiftOneotid; @(posedge clk) (areset) != 1'b1 && !(load)  && (ena) |-> shift_reg == {1'b0, shift_reg[3:1]}; endproperty 
 
 property ShiftSynceotid; @(posedge clk) (areset) != 1'b1 && !(load)  && !(ena) |-> shifted_value == {1'b0, shift_reg[3:1]}; endproperty 
 
 property ResetSynceotid; @(posedge clk) (areset) |-> q == 4'b0 ; endproperty 
 
 property ValidDataeotid; @(posedge clk) (areset) != 1'b1 && (load) && (ena)  |-> q == data ; endproperty 
 
 property SyncCheckeotid; @(posedge clk) (areset) != 1'b1 && !(load)  && !(ena) |-> q == shifted_value; endproperty 
 