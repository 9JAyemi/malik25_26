module sky130_fd_sc_lp__ha_sva (
    input logic A,
    input logic B,
    input logic COUT,
    input logic SUM,
    input logic and0_out_COUT,
    input logic xor0_out_SUM,
    input logic clk_signal_1
);

property SyncCheckeotid; @(posedge clk_signal_1) (A) && (B) |-> (and0_out_COUT) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_signal_1) (A) && (B) |-> (COUT) ;endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk_signal_1) (B) != (A) |-> (xor0_out_SUM) ;endproperty
assert property (SyncCheckeotid_3);

property SyncCheckeotid_4; @(posedge clk_signal_1) (B) != (A) |-> (SUM) ;endproperty
assert property (SyncCheckeotid_4);

endmodule