module top_module_sva (
    input logic clk,
    input logic count,
    input logic d,
    input logic en,
    input logic q,
    input logic reset
);

property ResetSynceotid; @(posedge clk) (reset) |-> (q == 0) ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (reset) |-> (count == 0) ;endproperty
assert property (ResetSynceotid_2);

property SyncLoadeotid; @(posedge clk) (en) && !(reset) |-> (q == d) ;endproperty
assert property (SyncLoadeotid);

property ClockSynceotid; @(posedge clk) (en) && !(reset) |-> (count == 1) ;endproperty
assert property (ClockSynceotid);

endmodule