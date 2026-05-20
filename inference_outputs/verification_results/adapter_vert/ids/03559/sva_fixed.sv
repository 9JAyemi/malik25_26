module MUXCY_sva (
    input logic A,
    input logic CO,
    input logic O,
    input logic B,
    input logic C,
    input logic D,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (O) |-> (A) ; endproperty
assert property (ClockSynceotid);

property SyncIneotid; @(posedge clk_in_1) (O) |-> (B) ; endproperty
assert property (SyncIneotid);

property SyncOuteotid; @(posedge clk_in_1) (O) == (A | B) ; endproperty
assert property (SyncOuteotid);

property SyncIneotid_2; @(posedge clk_in_1) (C) |-> (C) ; endproperty
assert property (SyncIneotid_2);

property SyncIneotid_3; @(posedge clk_in_1) (D) |-> (D) ; endproperty
assert property (SyncIneotid_3);

property SyncOuteotid_2; @(posedge clk_in_1) (CO) |-> (C) || (D) ; endproperty
assert property (SyncOuteotid_2);

endmodule