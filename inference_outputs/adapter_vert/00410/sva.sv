property ResetOnLoadSynceotid; @(posedge clk) (load) |-> out == 3'b000 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (load) != 1'b1 &&  (up_down) |-> out == data_15 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (load) != 1'b1 &&  !(up_down)  |-> out == data_14 ; endproperty 
 