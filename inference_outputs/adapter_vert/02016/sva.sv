property ResetSynceotid; @(posedge sys_clk) (sdram_rst) |-> counter == 3'd0 && precharge_safe == 1'b1 ;endproperty 
 
 property ClockSynceotid; @(posedge sys_clk) (sdram_rst) != 1'b1 &&  (read) |-> counter == 3'd4 && precharge_safe == 1'b0; endproperty 
 
 property WriteSynceotid; @(posedge sys_clk) (sdram_rst) != 1'b1 &&  (write) |-> counter == {1'b1, tim_wr} && precharge_safe == 1'b0; endproperty 
 
 property SyncSafeeotid; @(posedge sys_clk) (sdram_rst) != 1'b1 &&  !(read) &&  !(write)  &&  (counter == 3'b1) |-> precharge_safe == 1'b1; endproperty 
 
 property SyncSafeeotid; @(posedge sys_clk) (sdram_rst) != 1'b1 &&  !(read) &&  !(write)  &&  (counter != 3'b1)  |-> counter == counter - 3'b1 ; endproperty 
 