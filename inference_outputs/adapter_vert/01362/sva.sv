property AddSynceotid; @(posedge clk_in_1) (op) == (2'b00) |-> (result) == (A + B) ; endproperty 
 
 property SubSynceotid; @(posedge clk_in_1) (op) == (2'b01) |-> (result) == (A - B) ; endproperty 
 
 property MultSynceotid; @(posedge clk_in_1) (op) == (2'b10) |-> (result) == (A * B) ; endproperty 
 
 property DivSynceotid; @(posedge clk_in_1) (op) == (2'b11) |-> (result) == (A / B) ; endproperty 
 