module hpdmc_banktimer_sva (
    input logic counter,
    input logic precharge_safe,
    input logic read,
    input logic sdram_rst,
    input logic sys_clk,
    input logic tim_wr,
    input logic write,
    input logic b0,
    input logic b1,
    input logic d0,
    input logic d4
);

property ResetSynceotid; @(posedge sys_clk) (sdram_rst) |-> counter == 3'd0 && precharge_safe == 1'b1 ;endproperty
assert property (ResetSynceotid);

property ClockSynceotid; @(posedge sys_clk) (sdram_rst) != 1'b1 &&  (read) |-> counter == 3'd4 && precharge_safe == 1'b0; endproperty
assert property (ClockSynceotid);

property WriteSynceotid; @(posedge sys_clk) (sdram_rst) != 1'b1 &&  (write) |-> counter == {1'b1, tim_wr} && precharge_safe == 1'b0; endproperty
assert property (WriteSynceotid);

property SyncSafeeotid; @(posedge sys_clk) (sdram_rst) != 1'b1 &&  !(read) &&  !(write)  &&  (counter == 3'b1) |-> precharge_safe == 1'b1; endproperty
assert property (SyncSafeeotid);

property SyncSafeeotid_2; @(posedge sys_clk) (sdram_rst) != 1'b1 &&  !(read) &&  !(write)  &&  (counter != 3'b1)  |-> counter == counter - 3'b1 ; endproperty
assert property (SyncSafeeotid_2);

endmodule