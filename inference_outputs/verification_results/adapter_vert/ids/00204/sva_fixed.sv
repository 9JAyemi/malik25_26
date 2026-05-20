module debounce_sva (
    input logic clk,
    input logic pb,
    input logic pb_debounced,
    input logic shift_reg,
    input logic b0001,
    input logic b0010,
    input logic b0100,
    input logic b1,
    input logic b1000
);

property ClockSynceotid; @(posedge clk) (pb) |-> shift_reg == 4'b0001 ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk) (pb) |-> shift_reg == 4'b0010 ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk) (pb) |-> shift_reg == 4'b0100 ;endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk) (pb) |-> shift_reg == 4'b1000 ;endproperty
assert property (SyncCheckeotid_3);

property SyncDebounceeotid; @(posedge clk) (pb) |-> pb_debounced == 1'b1 ;endproperty
assert property (SyncDebounceeotid);

endmodule