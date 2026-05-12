property ClockSynceotid; @(posedge clock) (address) |-> (q == {address, 2'b00}); endproperty 
 
 property ClockSynceotid; @(posedge clock) (clock) |-> (q != address); endproperty 
 