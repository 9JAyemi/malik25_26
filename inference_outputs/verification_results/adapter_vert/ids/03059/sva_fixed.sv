module adder_module_sva (
    input logic clk,
    input logic d,
    input logic q,
    input logic reset
);

property ResetSynceotid; @(posedge clk) (reset) |-> (q == 0) ;endproperty
assert property (ResetSynceotid);

property SyncIniteotid; @(posedge clk) (reset) |-> (d == q) ;endproperty
assert property (SyncIniteotid);

property SyncIniteotid_2; @(posedge clk) (reset) |-> (q == 0) ;endproperty
assert property (SyncIniteotid_2);

property SyncIniteotid_3; @(posedge clk) (reset) |-> (d == q) ;endproperty
assert property (SyncIniteotid_3);

endmodule