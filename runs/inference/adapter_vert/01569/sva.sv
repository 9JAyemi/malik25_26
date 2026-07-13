property AdderSynceotid; @(posedge clk_in_16) (A) |-> (Sum) == ({1'b0, A} + {1'b0, B} + Cin); endproperty 
 
 property AdderSynceotid; @(posedge clk_in_16) (A) |-> (S) == (Sum[3:0]); endproperty 
 
 property AdderSynceotid; @(posedge clk_in_16) (A) |-> (Cout) == (Sum[4]); endproperty 
 