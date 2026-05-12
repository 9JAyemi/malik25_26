property LoadSynceotid; @(posedge clk) (load) |-> shift_reg == in ;endproperty 
 
 property ShiftOneotid; @(posedge clk) ( !load )  |-> shift_reg == {shift_reg[2:0], shift_reg[3]} ;endproperty 
 
 property SyncOuteotid; @(posedge clk) ( !load )  |-> ser_out_reg == shift_reg[3] ;endproperty 
 
 