property SyncCheckeotid; @(posedge clk_in_1) (a) and (b) |-> cout == 1'b1 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (a) != (b) |-> sum == 1'b1 ;endproperty 
 
 property ORSynceotid; @(posedge clk_in_1) (a_bitwise) |-> out_or_bitwise == (a_bitwise | b_bitwise) ;endproperty 
 
 property ORSynceotid; @(posedge clk_in_1) (a_bitwise) && (b_bitwise) |-> out_or_logical == 1'b1 ;endproperty 
 
 property NotSynceotid; @(posedge clk_in_1) (a_bitwise) || (b_bitwise) |-> out_not == 6'bxxxxxx ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (a) and (b) |-> out_sum == (sum + out_or_bitwise) ;endproperty 
 