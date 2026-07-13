module seq_detector_sva (
    input logic clk,
    input logic in,
    input logic out,
    input logic state,
    input logic b0,
    input logic b1,
    input logic next_state,
    input logic state0,
    input logic state1,
    input logic state2
);

property ResetSynceotid; @(posedge clk) (in) == (1'b0) && (state == state0) |-> next_state == state0 ; endproperty
assert property (ResetSynceotid);

property SyncCheckeotid; @(posedge clk) (in) != 1'b0 && (state == state0) |-> next_state == state1 ; endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk) (in) == 1'b0 && (state == state1) |-> next_state == state0 ; endproperty
assert property (SyncCheckeotid_2);

property SyncSafeeotid; @(posedge clk) (in) != 1'b0 && (state == state1) |-> next_state == state2 ; endproperty
assert property (SyncSafeeotid);

property SyncSafeeotid_2; @(posedge clk) (in) == 1'b0 && (state == state2) |-> next_state == state0 ; endproperty
assert property (SyncSafeeotid_2);

property SyncSafeeotid_3; @(posedge clk) (in) != 1'b0 && (state == state2) |-> next_state == state2 ; endproperty
assert property (SyncSafeeotid_3);

property SyncSafeeotid_4; @(posedge clk)  (state) == state0  |->  (out) == 1'b0 ; endproperty
assert property (SyncSafeeotid_4);

property ResetSynceotid_2; @(posedge clk)  (state) != state0  |->  (out) != 1'b1 ; endproperty
assert property (ResetSynceotid_2);

endmodule