property ResetSynceotid; @(posedge clk) (reset) |-> (counter_out) == (2'b0); endproperty 
 
 property ResetSynceotid; @(posedge clk) (reset) |-> (gray_out) == (2'b00); endproperty 
 
 property ResetSynceotid; @(posedge clk) (reset) |-> (q) == (8'b00000000); endproperty 
 
 property SyncCtrleotid; @(posedge clk) ( !reset ) && (  enable ) && (  up_down ) |-> (counter_out) == (counter_out + 2'b1); endproperty 
 
 property SyncCtrleotid; @(posedge clk) ( !reset ) && (  enable ) && ! (  up_down )  |-> (counter_out) == (counter_out - 2'b1); endproperty 
 
 property SyncCtrleotid; @(posedge clk) ( !reset ) &&  (  enable  &&  (  up_down  !=  7'b0100000  &&  up_down  !=  7'b1000000 )  ) |-> (gray_out) == (counter_out); endproperty 
 
 property SyncCtrleotid; @(posedge clk) ( !reset ) &&  (  enable  &&  (  up_down  !=  7'b0100000  &&  up_down  !=  7'b1000000 )  ) |-> (q) == ({gray_out, counter_out}); endproperty 
 