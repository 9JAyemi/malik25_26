module dffe_sva (
    input logic clk,
    input logic din,
    input logic en,
    input logic q,
    input logic se,
    input logic si,
    input logic so,
    input logic b1
);

property EnableSynceotid; @(posedge clk) (se) |-> q == si ; endproperty
assert property (EnableSynceotid);

property EnableSynceotid_2; @(posedge clk) (se) != 1'b1 &&  (en)  |-> q == din ; endproperty
assert property (EnableSynceotid_2);

property SyncOuteotid; @(posedge clk) (se) != 1'b1 &&  !(en)  |-> so == q ; endproperty
assert property (SyncOuteotid);

endmodule