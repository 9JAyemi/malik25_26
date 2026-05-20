module sky130_fd_sc_hvl__nand2_sva (
    input logic A,
    input logic B,
    input logic Y,
    input logic nand0_out_Y,
    input logic clk_in_19
);

property SyncIneotid; @(posedge clk_in_19) (Y) |-> (nand0_out_Y) &&  (B) &&  (A) ;endproperty
assert property (SyncIneotid);

property SyncSafeeotid; @(posedge clk_in_19) (Y) |-> (nand0_out_Y) ;endproperty
assert property (SyncSafeeotid);

endmodule