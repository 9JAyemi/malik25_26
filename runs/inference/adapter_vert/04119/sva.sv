property ResetSynceotid; @(posedge clk) (areset) |-> q == 4'b0000 ;endproperty 
 
 property LoadSynceotid; @(posedge clk) (areset) &&  (load) |-> q == data ;endproperty 
 
 property ValidDataeotid; @(posedge clk) (areset) &&  (!load) &&  (ena) |-> q == {q[2:0], q[3]};endproperty 
 