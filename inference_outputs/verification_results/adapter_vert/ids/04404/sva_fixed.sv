module or3_2_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic VGND,
    input logic VNB,
    input logic VPB,
    input logic VPWR,
    input logic X,
    input logic ab,
    input logic ac,
    input logic bc,
    input logic clk_in_19
);

property SyncIneotid; @(posedge clk_in_19) (A) && (B) |-> ab ; endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk_in_19) (B) && (C) |-> bc ; endproperty
assert property (SyncIneotid_2);

property SyncIneotid_3; @(posedge clk_in_19) (A) && (C) |-> ac ; endproperty
assert property (SyncIneotid_3);

property SyncIneotid_4; @(posedge clk_in_19) (ab) || (bc) || (ac) |-> X ; endproperty
assert property (SyncIneotid_4);

property PowerSynceotid; @(posedge clk_in_19)  (VGND) == (0) &&  (VPWR) == (1) &&  (VPB) == (1) &&  (VNB) == (0) ; endproperty
assert property (PowerSynceotid);

endmodule