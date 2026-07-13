property SplitIneotid; @(posedge clk_in_1) (in) |-> (out1) == (in[7:0]); endproperty 
 
 property SplitSynceotid; @(posedge clk_in_1) (in) |-> (out2) == (in[15:8]); endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (out2) &&  ( 0 ) |-> (out) == (and_gate_15); endproperty 
 