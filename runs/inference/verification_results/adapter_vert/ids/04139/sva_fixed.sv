module ZigbeeReceiver_sva (
    input logic carrier,
    input logic clk,
    input logic en,
    input logic modulated,
    input logic n,
    input logic out
);

property SyncDataeotid; @(posedge clk) (en && carrier) |-> out == {n{modulated}} ; endproperty
assert property (SyncDataeotid);

property SyncCheckeotid; @(posedge clk) (en && carrier) |-> out != 0 ; endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk) ! (en && carrier)  |-> out == 0; endproperty
assert property (SyncCheckeotid_2);

endmodule