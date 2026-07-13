property ClockSynceotid; @(posedge clk_in_1) (a) != (b) |-> (xor1_out) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (c) != (d) |-> (xor2_out) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_1) (xor1_out) && ( xor2_out) |-> (out_final) ;endproperty 
 