property ResetSynceotid; @(posedge clk) (rst) |-> (q == 1'b1) && (q_bar == 1'b0) ; endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) |-> (q != data) && (q_bar != data) ; endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) &&  (  data  != 0  &&  data  != 1  ) |-> (q != data) && (q_bar != data) ; endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) &&  (  data  == 0  ||  data  == 1  ) |-> (q == 1'b1) && (q_bar == 1'b0) ; endproperty 
 