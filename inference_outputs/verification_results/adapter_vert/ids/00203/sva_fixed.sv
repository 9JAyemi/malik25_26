module BusHold_sva (
    input logic clk,
    input logic hold,
    input logic in,
    input logic out,
    input logic rst,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (rst) |-> hold == 0 ;endproperty
assert property (ResetSynceotid);

property SyncLoadeotid; @(posedge clk) (rst) != 1'b1  |-> hold == in ;endproperty
assert property (SyncLoadeotid);

property SyncDataeotid; @(posedge clk) (rst) != 1'b1  |-> out == hold ;endproperty
assert property (SyncDataeotid);

endmodule