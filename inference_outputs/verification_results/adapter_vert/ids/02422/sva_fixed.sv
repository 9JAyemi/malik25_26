module sky130_fd_sc_hdll__nand4bb_sva (
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D,
    input logic Y,
    input logic nand0_out,
    input logic or0_out_Y,
    input logic clk_in_15
);

property SyncIneotid; @(posedge clk_in_15) (D) |-> (nand0_out) ;endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk_in_15) (B_N) && (A_N) &&  (C) |-> (or0_out_Y) ;endproperty
assert property (SyncIneotid_2);

property SyncSafeeotid; @(posedge clk_in_15) (or0_out_Y)  |-> (Y) ;endproperty
assert property (SyncSafeeotid);

endmodule