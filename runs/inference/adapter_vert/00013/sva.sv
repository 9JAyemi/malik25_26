property DataSynceotid; @(posedge clk_in_1) (sel) |-> (out) == (data1) ; endproperty 
 
 property DataSynceotid; @(posedge clk_in_1) (sel) != 1'b1  |-> (out) == (data0) ; endproperty 
 
 property DataSynceotid; @(posedge clk_in_1) (sel) &&  (data2)  &&  (data3)  |-> (out) == (data3) ; endproperty 
 
 property DataSynceotid; @(posedge clk_in_1) (sel) &&  (data2)  &&  !(data3)  |-> (out) == (data2) ; endproperty 
 