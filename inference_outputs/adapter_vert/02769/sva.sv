property ClockSynceotid; @(posedge clock_div_13) (Y) |-> (and0_out == (B1 && B2)) && (and1_out == (A1 && A2)) && (nor0_out_Y != (and0_out || C1 || and1_out)); endproperty 
 
 property ClockSynceotid; @(posedge clock_div_13) (Y) |-> (and0_out == (B1 && B2)) && (and1_out == (A1 && A2)) && (nor0_out_Y != (and0_out || C1 || and1_out)); endproperty 
 
 property SyncSafeeotid; @(posedge clock_div_13) (Y) |-> (and0_out == (B1 && B2)) && (and1_out == (A1 && A2)) && (nor0_out_Y != (and0_out || C1 || and1_out)); endproperty 
 