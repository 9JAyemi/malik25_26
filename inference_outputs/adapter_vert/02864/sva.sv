property ClockSynceotid; @(posedge clk) (sel) |-> (out == in2) ; endproperty 
 
 property SyncIneotid; @(posedge clk) (sel) != 1'b0  |-> (out == in1) ; endproperty 
 