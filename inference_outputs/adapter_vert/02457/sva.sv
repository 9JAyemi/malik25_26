property ClockSynceotid; @(posedge CLK) (SCE) |-> (D_ff == SCD) ;endproperty 
 
 property ClockSynceotid; @(posedge CLK) (SCE) != 1'b1  |-> (Q_ff == D_ff) ;endproperty 
 
 property ClockSynceotid; @(posedge CLK) (SCE) != 1'b1  |-> (Q == Q_ff) ;endproperty 
 
 property ClockSynceotid; @(posedge CLK) (SCE) != 1'b1  |-> (Q_N == ~Q_ff) ;endproperty 
 