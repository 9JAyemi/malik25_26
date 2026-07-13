module sky130_fd_sc_hd__a221oi_sva (
    input logic C1,
    input logic Y,
    input logic and0_out,
    input logic and1_out,
    input logic clk_osc_17
);

property ClockSynceotid; @(posedge clk_osc_17) (Y) |-> (and0_out) && (and1_out) && ( ! (and0_out) ||  ! (C1) &&  ! (and1_out) );endproperty
assert property (ClockSynceotid);

property SyncSafeeotid; @(posedge clk_osc_17) (Y) |-> (and0_out) && (and1_out) && ( ! (and0_out) ||  ! (C1) &&  ! (and1_out) );endproperty
assert property (SyncSafeeotid);

property SyncSafeeotid_2; @(posedge clk_osc_17) (Y) |-> (and0_out) && (and1_out) && ( ! (and0_out) ||  ! (C1) &&  ! (and1_out) );endproperty
assert property (SyncSafeeotid_2);

endmodule