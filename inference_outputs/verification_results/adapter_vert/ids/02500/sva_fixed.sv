module sky130_fd_sc_hdll__nand4bb_sva (
    input logic A_N,
    input logic B_N,
    input logic Y,
    input logic nand0_out,
    input logic or0_out_Y,
    input logic clk_in_14
);

property SyncIneotid; @(posedge clk_in_14) (Y) |-> (or0_out_Y == (B_N && A_N && nand0_out));endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk_in_14) (Y) |-> (or0_out_Y == (B_N && A_N && nand0_out));endproperty
assert property (SyncIneotid_2);

property SyncIneotid_3; @(posedge clk_in_14) (Y) |-> (or0_out_Y == (B_N && A_N && nand0_out));endproperty
assert property (SyncIneotid_3);

endmodule