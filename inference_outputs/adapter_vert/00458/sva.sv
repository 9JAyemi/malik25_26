property ClockSynceotid; @(posedge clk_in_1) (sel) |-> (out) == (in1) ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_1) (sel) != 1'b1  |-> (out) == (in0) ; endproperty 
 
 property SyncMuxeotid; @(posedge clk_in_1) (sel) != 1'b0  && @(posedge clk_in_1) (sel) != 1'b1  |-> (out) == (in2) ; endproperty 
 
 property SyncMuxeotid; @(posedge clk_in_1) (sel) == 2'b00  |-> (out) == (in3) ; endproperty 
 