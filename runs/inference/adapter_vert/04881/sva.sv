property ClockSynceotid; @(posedge clk) (Up) |-> (Q != 4'b1111) |-> Q == (Q + 1); endproperty 
 
 property ClockSynceotid; @(posedge clk) (Down) |-> (Q != 4'b0000) |-> Q == (Q - 1); endproperty 
 
 property ClockSynceotid; @(posedge clk) (Up) &&  (Q == 4'b1111) |-> Q == 4'b0000; endproperty 
 
 property ClockSynceotid; @(posedge clk) (Down) &&  (Q == 4'b0000) |-> Q == 4'b1111; endproperty 
 