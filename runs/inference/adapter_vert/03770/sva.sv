property ClockSynceotid; @(posedge clk) (in) |-> (out1 == in[7:0]) && (out2 == in[15:8]); endproperty 
 
 property ClockSynceotid; @(posedge clk) (in) |-> (out1) && (out2); endproperty 
 
 property ClockSynceotid; @(posedge clk) (in) |-> (out) == (in); endproperty 
 