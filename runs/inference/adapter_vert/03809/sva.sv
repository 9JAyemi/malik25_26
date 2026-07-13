property SubSynceotid; @(posedge clk_in_1) (SUB) |-> result == (A - B) && (  (result[3] == 1) ? 1 : 0 ) ;endproperty 
 
 property AddSynceotid; @(posedge clk_in_1) (SUB) != 1  |-> result == (A + B) && (  (result[3] == 1) ? 1 : 0 ) ;endproperty 
 