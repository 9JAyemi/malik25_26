module autoasciienum_onehot_sva (
    input logic ack,
    input logic clk,
    input logic cur_state,
    input logic rst_n,
    input logic b1,
    input logic h0,
    input logic h1,
    input logic nxt_state
);

property ResetSynceotid; @(posedge clk) (rst_n) |-> (nxt_state) == (5'h0) ; endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (rst_n) |-> (cur_state) == (5'b1) ; endproperty
assert property (ResetSynceotid_2);

property ValidAckeotid; @(posedge clk) (rst_n) &&  (  (cur_state) == (5'b1)  &&  (nxt_state) == (5'h1)  ) |->  (ack) == 1'b1 ; endproperty
assert property (ValidAckeotid);

property ValidStateeotid; @(posedge clk) (rst_n) &&  (  (cur_state) != 5'b1  ||  (nxt_state) != 5'h1  ) |->  (ack) != 1'b1 ; endproperty
assert property (ValidStateeotid);

property SyncStateeotid; @(posedge clk) (rst_n) |-> (nxt_state) == (cur_state) ; endproperty
assert property (SyncStateeotid);

property SyncStateeotid_2; @(posedge clk) (rst_n) &&  (  (cur_state) != 5'b1  ||  (nxt_state) != 5'h1  ) |->  (cur_state) != 5'b1 ; endproperty
assert property (SyncStateeotid_2);

property SyncStateeotid_3; @(posedge clk) (rst_n) &&  (  (cur_state) != 5'b1  ||  (nxt_state) != 5'h1  ) &&  (  (cur_state) != 5'b1  ||  (nxt_state) != 5'h1  ) |->  (nxt_state) != 5'h1 ; endproperty
assert property (SyncStateeotid_3);

endmodule