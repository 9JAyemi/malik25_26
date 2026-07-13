module dual_edge_triggered_ff_sva (
    input logic clk,
    input logic d,
    input logic q,
    input logic q1,
    input logic q2
);

property ClockSynceotid; @(posedge clk) (d) |-> (q1) ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(negedge clk) (q1) |-> (q2) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(negedge clk) (q2) == (q) ;endproperty
assert property (SyncCheckeotid_2);

endmodule