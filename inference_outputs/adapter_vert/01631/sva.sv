property ClockSynceotid; @(posedge clk_osc_17) (X) |-> (nand0_out == 1'b1) && (or0_out == 1'b1) && (and0_out_X == 1'b1); endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_17) (X) |-> (nand0_out == 1'b1) && (or0_out == 1'b1) && (and0_out_X == 1'b1); endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_17) (X) |-> (nand0_out == 1'b1) && (or0_out == 1'b1) && (and0_out_X == 1'b1); endproperty 
 