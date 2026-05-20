module register_4bit_sva (
    input logic Q,
    input logic Q_reg,
    input logic clk,
    input logic data_in,
    input logic load,
    input logic reset,
    input logic b0
);

property ResetSynceotid; @(posedge clk) (reset) |-> Q_reg == 4'b0 ;endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge clk) (load) && !(reset) |-> Q_reg == data_in ;endproperty
assert property (LoadSynceotid);

property SyncLoadeotid; @(posedge clk) (reset) && !(load) |-> Q == 4'b0 ;endproperty
assert property (SyncLoadeotid);

endmodule