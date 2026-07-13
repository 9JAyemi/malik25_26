module sky130_fd_sc_hs__nand2b_sva (
    input logic A_N,
    input logic B,
    input logic Y,
    input logic clk_osc_11
);

property SyncCheckeotid; @(posedge clk_osc_11) (A_N) && (  B ) |->  ! ( Y ) ;endproperty
assert property (SyncCheckeotid);

property SyncSafeeotid; @(posedge clk_osc_11) (A_N) || (  B ) |->  ( Y ) ;endproperty
assert property (SyncSafeeotid);

endmodule