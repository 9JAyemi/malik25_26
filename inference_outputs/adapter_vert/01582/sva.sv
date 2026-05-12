property ResetSynceotid; @(posedge clk) (reset) |-> Q_reg == 4'b0 ;endproperty 
 
 property LoadSynceotid; @(posedge clk) (load) && !(reset) |-> Q_reg == data_in ;endproperty 
 
 property SyncLoadeotid; @(posedge clk) (reset) && !(load) |-> Q == 4'b0 ;endproperty 
 