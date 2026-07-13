module sky130_fd_sc_hd__nor4_sva (
    input logic Y,
    input logic nor0_out_Y,
    input logic clk_in_17
);

property ClockSynceotid; @(posedge clk_in_17) (Y) |-> (nor0_out_Y) ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_in_17) (Y) |-> (Y) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_17) (Y) |-> (nor0_out_Y) ;endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk_in_17) (Y) |-> (Y) ;endproperty
assert property (SyncCheckeotid_3);

endmodule