module sync_up_down_counter_sva (
    input logic clk,
    input logic q,
    input logic up_down,
    input logic data_14
);

property SyncUpeotid; @(posedge clk) (up_down) |-> (q != 7) ; endproperty
assert property (SyncUpeotid);

property SyncDowneotid; @(posedge clk) (up_down) &&  (q == 7) |-> (q == 0) ; endproperty
assert property (SyncDowneotid);

property SyncUpeotid_2; @(posedge clk) ! (up_down)  &&  (q != 7) |-> (q == data_14) ; endproperty
assert property (SyncUpeotid_2);

property SyncDowneotid_2; @(posedge clk) ! (up_down)  &&  (q == 7) |-> (q == 6) ; endproperty
assert property (SyncDowneotid_2);

endmodule