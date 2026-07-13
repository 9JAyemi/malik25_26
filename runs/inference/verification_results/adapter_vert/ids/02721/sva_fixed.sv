module dffre_sva (
    input logic clk,
    input logic din,
    input logic en,
    input logic q,
    input logic rst,
    input logic se,
    input logic si,
    input logic so,
    input logic b0,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (se) |-> q == si ; endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (se) != 1'b1 && (rst) |-> q == 1'b0 ; endproperty
assert property (ResetSynceotid_2);

property ValidDataeotid; @(posedge clk) (se) != 1'b1 && !(rst) && (en) |-> q == din ; endproperty
assert property (ValidDataeotid);

property SyncOuteotid;  @(posedge clk) (se) != 1'b1 && !(rst) && !(en)  |-> so == q; endproperty
assert property (SyncOuteotid);

endmodule