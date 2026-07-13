property ResetSynceotid; @(posedge clk) (reset) |-> count_reg == 4'b0000 ;endproperty 
 
 property LoadSynceotid; @(posedge clk) (load) |-> count_next == count ;endproperty 
 
 property SyncUpeotid; @(posedge clk) ( !load ) && (  up_down ) |-> count_next == count_reg + 4'b0001 ;endproperty 
 
 property SyncDowneotid; @(posedge clk) ( !load ) && ( !up_down )  |-> count_next == count_reg - 4'b0001; endproperty 
 
 property SyncCtrleotid; @(posedge clk)  (  count  !=  count_reg  ) |->  (  !load ) && (  up_down ) ;endproperty 
 