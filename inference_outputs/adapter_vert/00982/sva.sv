property ResetSynceotid; @(posedge clk) (rst) |-> (contents) == (RESET_VAL); endproperty 
 
 property EnableSynceotid; @(posedge clk) (rst) != 1'b1 && (en) |-> (contents) == (d); endproperty 
 
 property SyncLoadeotid; @(posedge clk) (rst) != 1'b1  |-> (q) == (contents); endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) |-> (contents) == (d) ; endproperty 
 
 property SyncLoadeotid; @(posedge clk)  |-> (q) == (contents); endproperty 
 