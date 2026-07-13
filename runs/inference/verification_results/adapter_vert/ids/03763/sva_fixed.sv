module fill_diode_sva (
    input logic VGND,
    input logic VNB,
    input logic VPB,
    input logic VPWR,
    input logic fill,
    input logic clk_in_15
);

property PowerSynceotid; @(posedge clk_in_15) (VPWR) |-> (fill) ;endproperty
assert property (PowerSynceotid);

property SafeStarteotid; @(posedge clk_in_15) (VGND) |-> ! (fill) ;endproperty
assert property (SafeStarteotid);

property SyncCheckeotid; @(posedge clk_in_15) (VPB) |-> ! (fill) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_15) (VNB) |->  (fill) ;endproperty
assert property (SyncCheckeotid_2);

endmodule