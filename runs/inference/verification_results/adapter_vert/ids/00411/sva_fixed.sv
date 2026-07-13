module lfsr_counter_sva (
    input logic clk,
    input logic ena,
    input logic reset,
    input logic state,
    input logic data
);

property ResetSynceotid; @(posedge clk) (reset) |-> state == 0 ;endproperty
assert property (ResetSynceotid);

property ValidCtrleotid; @(posedge clk) (reset) &&  (ena) |-> state == data ;endproperty
assert property (ValidCtrleotid);

property ClockSynceotid; @(posedge clk) (reset) &&  (!ena) |-> data == 0 ;endproperty
assert property (ClockSynceotid);

endmodule