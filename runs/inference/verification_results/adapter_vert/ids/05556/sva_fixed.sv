module sequence_edge_detection_sva (
    input logic change_out,
    input logic clk,
    input logic final_out,
    input logic in,
    input logic out,
    input logic prev_in,
    input logic reset,
    input logic seq_out,
    input logic b0
);

property ResetSynceotid; @(posedge clk) (reset) |-> (out) == (4'b0) && (prev_in) == (4'b0); endproperty
assert property (ResetSynceotid);

property SyncChangeeotid; @(posedge clk) (reset) |-> (out) == (32'b0) && (prev_in) == (32'b0); endproperty
assert property (SyncChangeeotid);

property SyncCheckeotid; @(posedge clk) (in[3:0] != prev_in) |-> (out) == (in[3:0]) && (prev_in) == (in[3:0]); endproperty
assert property (SyncCheckeotid);

property SyncChangeeotid_2; @(posedge clk) (in[35:4] != prev_in) |-> (out) == (prev_in & ~in[35:4]) && (prev_in) == (in[35:4]); endproperty
assert property (SyncChangeeotid_2);

property SyncCheckeotid_2; @(posedge clk) (seq_out | change_out) |-> (final_out) == (seq_out | change_out); endproperty
assert property (SyncCheckeotid_2);

endmodule