property ClockSynceotid; @(posedge clk) (a) != (b) |-> (out) == 1'b1 ; endproperty 
 
 property SyncEqeotid; @(posedge clk) (a) == (b) |-> (out) == 1'b0 ; endproperty 
 
 property DataSynceotid; @(posedge clk) (a) != (b) &&  (a) != (mux_in)  |->  (sel) != 2'b00 ; endproperty 
 
 property SyncCheckeotid; @(posedge clk) (a) != (b) &&  (b) != (mux_in)  |->  (sel) != 2'b01 ; endproperty 
 
 property SyncCheckeotid; @(posedge clk) (a) != (b) &&  (a) != (mux_in)  &&  (b) != (mux_in)  |->  (sel) != 2'b10 ; endproperty 
 
 property SyncCheckeotid; @(posedge clk) (a) != (b) &&  (a) != (mux_in)  &&  (b) != (mux_in)  |->  (sel) == 2'b11 ; endproperty 
 