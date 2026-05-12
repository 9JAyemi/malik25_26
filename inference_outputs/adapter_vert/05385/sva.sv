property ClockSynceotid; @(posedge CLK1) (A1EN) |-> mem[A1ADDR] == A1DATA ;endproperty 
 
 property SyncLoadeotid; @(posedge CLK1) (B1ADDR) |-> B1DATA == mem[B1ADDR] ;endproperty 
 