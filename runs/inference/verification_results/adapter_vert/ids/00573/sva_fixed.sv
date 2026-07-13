module sky130_fd_sc_hd__nor4b_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D_N,
    input logic Y,
    input logic clk_osc_19
);

property ClockSafeeotid; @(posedge clk_osc_19) (Y) |-> ! ( A ) && ! ( B ) && ! ( C ) &&  ( D_N ) ;endproperty
assert property (ClockSafeeotid);

property SyncSafeeotid; @(posedge clk_osc_19) (Y) |->  ( A ) ||  ( B ) ||  ( C ) || ! ( D_N ) ;endproperty
assert property (SyncSafeeotid);

property ClockSafeeotid_2; @(posedge clk_osc_19) (Y) |->  ( A ) &&  ( B ) &&  ( C ) && ! ( D_N ) ;endproperty
assert property (ClockSafeeotid_2);

property SyncSafeeotid_2; @(posedge clk_osc_19) (Y) |-> ! ( A ) &&  ( B ) &&  ( C ) && ! ( D_N ) ;endproperty
assert property (SyncSafeeotid_2);

endmodule