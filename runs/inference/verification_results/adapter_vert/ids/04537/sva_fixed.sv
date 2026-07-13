module EtherCAT_slave_sva (
    input logic clk,
    input logic in_receive,
    input logic out_send,
    input logic rst,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (rst) |-> (out_send == 0) ;endproperty
assert property (ResetSynceotid);

property SyncRxeotid; @(posedge clk) (rst) != 1'b1 |-> (out_send == in_receive) ;endproperty
assert property (SyncRxeotid);

endmodule