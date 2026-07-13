module Test_sva (
    input logic a,
    input logic b,
    input logic out,
    input logic b0000000,
    input logic clk_in_1
);

property SyncEqeotid; @(posedge clk_in_1) (a) == (b) |-> (out) == (a) ; endproperty
assert property (SyncEqeotid);

property SyncGoeotid; @(posedge clk_in_1) (a) != (b) && (a) >= (b) |-> (out) == (a) ; endproperty
assert property (SyncGoeotid);

property SyncGoeotid_2; @(posedge clk_in_1) (a) != (b) && (b) > (a) |-> (out) == (b) ; endproperty
assert property (SyncGoeotid_2);

property SyncCheckeotid; @(posedge clk_in_1) (a) != (b) && (a) < (b)  |-> (out) == 7'b0000000 ; endproperty
assert property (SyncCheckeotid);

endmodule