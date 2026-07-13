module rising_edge_detector_sva (
    input logic clk,
    input logic in,
    input logic out,
    input logic prev_state,
    input logic reset
);

property ResetSynceotid; @(posedge clk) (reset) |-> (prev_state == 0) && (out == 0) ;endproperty
assert property (ResetSynceotid);

property SyncIneotid; @(posedge clk) ( !reset ) |-> ( prev_state == in ) && ( out == (in & ~prev_state) ) ;endproperty
assert property (SyncIneotid);

endmodule