module logic_module_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F,
    input logic G,
    input logic H,
    input logic X,
    input logic and0_out,
    input logic and1_out,
    input logic or0_out,
    input logic or1_out,
    input logic clk_in_11
);

property ClockSynceotid; @(posedge clk_in_11) (A) and (B) |-> and0_out ; endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_in_11) (C) and (D) |-> or0_out ; endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_11) (E) and (F) |-> and1_out ; endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk_in_11) (G) and (H) |-> or1_out ; endproperty
assert property (SyncCheckeotid_3);

property SyncSafeeotid; @(posedge clk_in_11) (and0_out || or0_out || !and1_out || !or1_out) == (X) ; endproperty
assert property (SyncSafeeotid);

endmodule