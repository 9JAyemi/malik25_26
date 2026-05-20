module zbroji_sva (
    input logic a,
    input logic b,
    input logic sum,
    input logic clk_in_17
);

property AddSynceotid; @(posedge clk_in_17) (a) |-> (sum) ;endproperty
assert property (AddSynceotid);

property SyncAddereotid; @(posedge clk_in_17) (b) |-> (sum) ;endproperty
assert property (SyncAddereotid);

endmodule