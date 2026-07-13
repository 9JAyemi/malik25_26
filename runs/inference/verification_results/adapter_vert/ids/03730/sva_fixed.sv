module d_to_t_ff_sva (
    input logic clk,
    input logic d,
    input logic q,
    input logic t
);

property ClockSynceotid; @(posedge clk) (d) |-> (t) ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk) (d) != (q) |-> (t) ;endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk) (d) != (q) |-> (q) ;endproperty
assert property (SyncCheckeotid_3);

endmodule