property ClockSynceotid; @(posedge clk) (shift_dir) |-> in == reg1 && reg1 == reg2 && reg2 == reg3 ; endproperty 
 
 property ShiftSynceotid; @(posedge clk) ( !shift_dir ) |-> reg4 == reg3 && reg3 == reg2 && reg2 == in ; endproperty 
 
 property SyncIniteotid; @(posedge clk)  (  shift_dir  !=  1  &&  reg4  !=  reg3 ) |-> reg4 == reg3 && reg3 == reg2 && reg2 == reg1 ; endproperty 
 
 property SyncIniteotid; @(posedge clk)  (  reg4  !=  reg3  || reg3  !=  reg2  || reg2  !=  reg1  ||  reg1  !=  in ) |-> reg4 == reg3 && reg3 == reg2 && reg2 == in ; endproperty 
 