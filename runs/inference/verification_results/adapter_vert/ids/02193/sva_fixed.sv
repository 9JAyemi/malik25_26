module dff_module_sva (
    input logic clk,
    input logic d,
    input logic q
);

property ClockSynceotid; @(negedge clk) (d) |-> (q) ;endproperty
assert property (ClockSynceotid);

property SyncLoadeotid; @(negedge clk) (d) |-> (q) ;endproperty
assert property (SyncLoadeotid);

endmodule