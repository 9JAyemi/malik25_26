property AddSynceotid; @(posedge clk_in_1) (SUB) |-> (SUM) == (A + B_comp); endproperty 
 
 property SubSynceotid; @(posedge clk_in_1) (SUB) != 1'b1  |-> (SUM) == (A + B); endproperty 
 
 