property LoadSynceotid; @(posedge clk) (load) |-> Q == input_data ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (load) != 1'b1  &&  (up_down) |-> Q == (Q + 1) ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (load) != 1'b1  &&  !(up_down)  |-> Q == (Q - 1) ; endproperty 
 