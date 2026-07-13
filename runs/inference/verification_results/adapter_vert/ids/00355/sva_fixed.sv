module m_pc_reg_sva (
    input logic r_bus_addr_out,
    input logic w_bus_addr_in,
    input logic w_clock,
    input logic w_reset,
    input logic b0,
    input logic b1
);

property ResetSynceotid; @(posedge w_clock) (w_reset) |-> r_bus_addr_out == 8'b0 ;endproperty
assert property (ResetSynceotid);

property SyncLoadeotid; @(posedge w_clock) (w_reset) != 1'b1  |-> r_bus_addr_out == w_bus_addr_in; endproperty
assert property (SyncLoadeotid);

endmodule