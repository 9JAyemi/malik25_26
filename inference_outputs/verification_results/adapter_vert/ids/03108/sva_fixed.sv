module dual_d_flip_flop_sva (
    input logic clk,
    input logic d_ff_1,
    input logic d_in,
    input logic reset,
    input logic toggle,
    input logic b0,
    input logic d_ff_2
);

property ResetSynceotid; @(posedge clk) (reset) |-> (d_ff_1 == 1'b0) && (d_ff_2 == 1'b0) ;endproperty
assert property (ResetSynceotid);

property SyncIneotid; @(posedge clk) ( !reset ) |-> (d_ff_1 == d_in) && (d_ff_2 == toggle) ;endproperty
assert property (SyncIneotid);

endmodule