module up_down_counter_sva (
    input logic clk,
    input logic count,
    input logic data_in,
    input logic load,
    input logic reset,
    input logic up_down,
    input logic b0,
    input logic reg_13,
    input logic reg_15
);

property ResetSynceotid; @(posedge clk) (reset) |-> count == 4'b0 ;endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge clk) (load) |-> count == data_in ;endproperty
assert property (LoadSynceotid);

property IncrCtrleotid; @(posedge clk) (up_down) && ! (reset) && ! (load)  |-> count == reg_13 ;endproperty
assert property (IncrCtrleotid);

property DecrCtrleotid; @(posedge clk) ! (up_down) && ! (reset) && ! (load)  |-> count == reg_15 ;endproperty
assert property (DecrCtrleotid);

endmodule