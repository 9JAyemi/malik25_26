property AddSynceotid; @(posedge clk) (op) |-> result == a - b ; endproperty 
 
 property AddSynceotid; @(posedge clk) (op) != 1 |-> result == a + b ; endproperty 
 
 property SafeSynceotid; @(posedge clk) (result[7] == 1 && op == 0 && a[7] == 1 && b[7] == 1) || (result[7] == 1 && op == 1 && a[7] == 0 && b[7] == 1) || (result[7] == 0 && op == 1 && a[7] == 1 && b[7] == 0) |-> overflow == 1 ; endproperty 
 